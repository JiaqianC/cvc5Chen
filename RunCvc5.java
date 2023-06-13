package aprove.GraphUserInterface.Factories.Solvers.Engines;


import java.io.*;
import java.util.*;
import java.util.concurrent.TimeUnit;

import aprove.Framework.Utility.GenericStructures.*;
import aprove.Strategies.Abortions.*;

public class RunCvc5 {

    public static void main(String[] args) {
        
        String problem = 
                "(set-logic QF_LIA)\n"+
                "(declare-fun x () Int)\n"+
                "(assert (<= x 0))\n"+
                "(assert (not (= (- x) (abs x))))\n"+
                "(check-sat)\n";
                //"(exit)\n";
        
        //System.out.println(problem);

        try {
            String result = runCvc(problem);
            List<String> stringList = new ArrayList<>();
            System.out.println(result);
            System.out.println("++++++++++++");
            
            stringList.add(result);
            Pair<List<String>, List<String>> lines = new Pair<>(stringList,new ArrayList<>());
            System.out.println(lines);
        } catch (IOException | InterruptedException e) {
            e.printStackTrace();
        }
    }
    /*
    public static Pair<List<String>, List<String>> torunYices(String cmd, final Abortion aborter){
        Triple<Integer, List<String>, List<String>> res = runYices(cmd, Collections.emptyMap(), aborter);
        return new Pair<List<String>, List<String>>(res.y, res.z);
        
    }
    */

    public static String runCvc(String input) throws IOException, InterruptedException {
        ProcessBuilder builder = new ProcessBuilder("cvc5","--produce-models");
        //ProcessBuilder builder = new ProcessBuilder("yices","--mode=one-shot");
        builder.redirectErrorStream(true);

        Process process = builder.start();
        InputStream inputStream = process.getInputStream();
        BufferedReader reader = new BufferedReader(new InputStreamReader(inputStream));

        process.getOutputStream().write(input.getBytes());
        process.getOutputStream().flush();
        process.getOutputStream().close();

        process.waitFor(1, TimeUnit.SECONDS);

        StringBuilder output = new StringBuilder();
        String line;
        while ((line = reader.readLine()) != null) {
            output.append(line).append("\n");
        }

        process.destroy();

        return output.toString();
    }
}
