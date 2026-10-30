-- Prove2me | Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram_prepareProgram_factored_runsIn
-- name    : OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T00:02:54.168986+00:00
-- url     : https://prove2.me/theorems/05787041-be24-4b83-873f-02e51e3a90a9
-- title:
--   OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn: intermediate lemma from OpenAI, The Exponential Time Hypothesis is False
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Exponential Time Hypothesis is False*, OpenAI Math Release, October 25, 2026, result family 378, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn` of [lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram`, with `open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram`):
--
--   ```lean
--   theorem prepareProgram_factored_runsIn (c : Cache) (regs : Fin 9 → Bool)
--       (counter parity : List Bool) (A R d h : ℕ)
--       (hc : counter.length = R-d) (ha : parity.length = A)
--       (hu : c.Uniform) (hf : c.Fits (R-d))
--       (hv : c.Values A R h) (hm : c.Totals A R h) :
--       ∃ r xs,
--         RunsIn prepareProgram
--           (9*(R-d)+3*A+(R-d)*((R-d)*(28*c.width.length+34)+140*c.width.length+
--             18*pairLength c.power+222)+3*((R-d)*(8*c.width.length+2*pairLength c.power+9))+24)
--           ((cacheState c regs counter [] [] [] [] parity).withPC (some prepareProgram.entry))
--           ((cacheState c r [] [] [] []
--             (pairEncoding (LayoutProgramScalar.tripleWords xs)) []).withPC none) ∧
--         FactoredEncodes A R d h xs ∧ FactoredTotalEncodes A R d h xs ∧
--         LayoutProgramScalar.Bounded (2*c.width.length+pairLength c.power) xs ∧
--         (xs.map LayoutProgramScalar.termValue).sum = LayoutCoefficientAlgorithm.scalarSum A R d h ∧
--         (xs.map LayoutProgramScalar.termTotal).sum = LayoutProgram.scalarMass R d h
--           (fun j => (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Algorithms.SubexponentialSAT.StructuredCalls.size`, `OAI.Algorithms.SubexponentialSAT.BitProgram.Program` and `OAI.Algorithms.SubexponentialSAT.StructuredProgram.State.withPC` (definitions bundle `OAIQ081S000` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.coefficientAt` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutCoefficientAlgorithm.scalarSum` (definitions bundle `OAIQ081S003` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.scalarMass` (definitions bundle `OAIQ081S014` of this split); `OAI.Algorithms.SubexponentialSAT.BitProgram.RunsIn` (definitions bundle `OAIQ081S023` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairEncoding` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.pairLength` (definitions bundle `OAIQ081S034` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Triple` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.tripleWords` (definitions bundle `OAIQ081S036` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Fits` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Uniform` (definitions bundle `OAIQ081S058` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepare` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram` (definitions bundle `OAIQ081S073` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.Bounded`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termTotal`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.termValue`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.FactoredEncodes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.FactoredTotalEncodes`, `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Totals` and `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.Cache.Values` (definitions bundle `OAIQ081S075` of this split); `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.cacheState` (definitions bundle `OAIQ081S091` of this split).
--
--   **Used by.** The proof of `OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.FromCounts.numerator_eval` of this split imports it.
-- source:
--   OpenAI, The Exponential Time Hypothesis is False, OpenAI Math Release, October 25, 2026, https://github.com/openai/math (result family 378; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Algorithms/SubexponentialSAT/SqrtLog/LayoutTriplePreparationProgramInterface.lean (declaration OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.prepareProgram_factored_runsIn)

import Mathlib
import Definitions.Def_OAIQ081S091

section

attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem prepareProgram_factored_runsIn (c : Cache) (regs : Fin 9 → Bool)
    (counter parity : List Bool) (A R d h : ℕ)
    (hc : counter.length = R-d) (ha : parity.length = A)
    (hu : c.Uniform) (hf : c.Fits (R-d))
    (hv : c.Values A R h) (hm : c.Totals A R h) :
    ∃ r xs,
      RunsIn prepareProgram
        (9*(R-d)+3*A+(R-d)*((R-d)*(28*c.width.length+34)+140*c.width.length+
          18*pairLength c.power+222)+3*((R-d)*(8*c.width.length+2*pairLength c.power+9))+24)
        ((cacheState c regs counter [] [] [] [] parity).withPC (some prepareProgram.entry))
        ((cacheState c r [] [] [] []
          (pairEncoding (LayoutProgramScalar.tripleWords xs)) []).withPC none) ∧
      FactoredEncodes A R d h xs ∧ FactoredTotalEncodes A R d h xs ∧
      LayoutProgramScalar.Bounded (2*c.width.length+pairLength c.power) xs ∧
      (xs.map LayoutProgramScalar.termValue).sum = LayoutCoefficientAlgorithm.scalarSum A R d h ∧
      (xs.map LayoutProgramScalar.termTotal).sum = LayoutProgram.scalarMass R d h
        (fun j => (LayoutCoefficientAlgorithm.coefficientAt A R j).natAbs) := by
  sorry

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end
