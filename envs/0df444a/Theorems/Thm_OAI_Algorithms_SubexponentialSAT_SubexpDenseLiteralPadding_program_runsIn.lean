-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SubexpDenseLiteralPadding_program_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T23:56:40.037598+00:00
-- url     : https://prove2.me/theorems/a0957b7f-fef6-4511-b63e-52fed44cffa7
-- title:
--   OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SubexpDenseLiteralPadding.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpDenseLiteralPadding.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding`, with `open BitProgram StructuredCalls ModularArithmetic ModularPrograms`, `open SubexpConvolutionControl (Store Code )`):
--
--   ```lean
--   theorem program_runsIn (s : Store) (regs : Fin 16 → Bool) (bits tail : List Bool)
--       (hin : s 27 = true :: (Encoding.frame bits ++ tail))
--       (h21 : s 21 = []) (h29 : s 29 = []) (h99 : s 99 = []) (h120 : s 120 = []) :
--       RunsIn program (12 * bits.length + 16 * (s 242).length + 46)
--         ((⟨regs, s⟩ : State 16 256).withPC (some program.entry))
--         ((⟨fun _ => false,
--           Function.update s 27 (true :: (Encoding.frame (padTo (s 242) bits) ++ tail))⟩ :
--             State 16 256).withPC none)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program`, `OAI.Algorithms.SubexponentialSAT.StructuredCalls.Cmd`, `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.ModularArithmetic.padTo` (definitions bundle `OAIQ081S002` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpConvolutionControl.Store` (definitions bundle `OAIQ081S004` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.command`, `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program` and `OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.reset` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.Encoding.frame` (the published bundle `Def_SubexponentialSAT`).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.PolynomialExecutorProgram.load_implements` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SubexpDenseLiteralPadding.lean (declaration OAI.Algorithms.SubexponentialSAT.SubexpDenseLiteralPadding.program_runsIn)

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S075

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SubexpDenseLiteralPadding

open BitProgram StructuredCalls ModularArithmetic ModularPrograms
open SubexpConvolutionControl (Store Code )

theorem program_runsIn (s : Store) (regs : Fin 16 → Bool) (bits tail : List Bool)
    (hin : s 27 = true :: (Encoding.frame bits ++ tail))
    (h21 : s 21 = []) (h29 : s 29 = []) (h99 : s 99 = []) (h120 : s 120 = []) :
    RunsIn program (12 * bits.length + 16 * (s 242).length + 46)
      ((⟨regs, s⟩ : State 16 256).withPC (some program.entry))
      ((⟨fun _ => false,
        Function.update s 27 (true :: (Encoding.frame (padTo (s 242) bits) ++ tail))⟩ :
          State 16 256).withPC none) := by
  sorry

end SubexponentialSAT.SubexpDenseLiteralPadding

end OAI.Algorithms
end
