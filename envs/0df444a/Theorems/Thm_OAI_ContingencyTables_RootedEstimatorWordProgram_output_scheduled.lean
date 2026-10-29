-- Prove2me | Theorems.Thm_OAI_ContingencyTables_RootedEstimatorWordProgram_output_scheduled
-- name    : OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:03:11.503559+00:00
-- url     : https://prove2.me/theorems/b8e15795-511b-4ac0-8592-7ef254aa72b9
-- title:
--   OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled` of [lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorWordLaw.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorWordLaw.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.RootedEstimatorWordProgram`, with `open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary`, `open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem output_scheduled (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
--       (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
--       (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
--       (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
--       (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
--       (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
--       (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
--       (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
--       (bits : Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) :
--       TreeFraction.val (output (input (scheduledContext A C K j delta failure z v)
--         (degree,depth) bits))=RootedComputedEstimator.estimate A C K j hK hW delta failure z v
--           (scheduledEquiv A C K j delta failure z v bits)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ContingencyTables.BalancedBox.InBox` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.View`, `OAI.ContingencyTables.CompanionFactorialApplication.bounds`, `OAI.ContingencyTables.CompanionOracleDensity.binWidth`, `OAI.ContingencyTables.CompanionOracleDensity.rationalHeight`, `OAI.ContingencyTables.CompanionOracleDensity.roundingTolerance`, `OAI.ContingencyTables.GridBoundary.Grid`, `OAI.ContingencyTables.PowerOfTwoApproximation.depth`, `OAI.ContingencyTables.PowerOfTwoApproximation.rootDegree`, `OAI.ContingencyTables.RootedCatalogGrid.freeCount` and `OAI.MatchingFPRAS.TreeFraction.val` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.RootedEstimatorLayoutProgram.wordWidth`, `OAI.ContingencyTables.RootedEstimatorWordProgram.output` and `OAI.ContingencyTables.RootedEstimatorWordProgram.scheduledContext` (definitions bundle `OAIQ089A003` of this split); `OAI.ContingencyTables.RootedComputedEstimator.Inputs`, `OAI.ContingencyTables.RootedEstimatorWordProgram.input` and `OAI.ContingencyTables.RootedEstimatorWordProgram.scheduledEquiv` (definitions bundle `OAIQ089A008` of this split); `OAI.ContingencyTables.RootedComputedEstimator.estimate` (definitions bundle `OAIQ089A009` of this split).
--
--   **Used by.** The proofs of `OAI.ContingencyTables.CompanionPhaseContinuation.run_sameLaw`, `OAI.ContingencyTables.CompanionRestartProgram.output_native_sameLaw` and `OAI.ContingencyTables.counting` of this split import it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorWordLaw.lean (declaration OAI.ContingencyTables.RootedEstimatorWordProgram.output_scheduled)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009

section

attribute [-instance] _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.RootedEstimatorWordProgram

open MatchingFPRAS CompanionFactorialApplication ForestAssignmentSplit GridBoundary
open CompanionOracleDensity RootedEstimatorLayoutProgram CommonBasesFPRAS
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

theorem output_scheduled (A : Instance (Fin m) (Fin n)) (C K j : ℕ)
    (hC : 0 < C) (hj : j ≤ rationalHeight A C) (hK : 1 ≤ K)
    (hW : 100*A.d*K ≤ A.W) (hB : (K:ℝ)=CompanionOracleDensity.binWidth A C)
    (delta failure : ℚ) (hd : 0 < delta) (hf : 0 < failure)
    (z : View A → ℕ) (hz : BalancedBox.InBox (bounds A) z)
    (v : Grid (I := Fin (RootedCatalogGrid.freeCount A)) K) (degree depth : List Bool)
    (hdegree : degree.length=PowerOfTwoApproximation.rootDegree (roundingTolerance delta))
    (hdepth : depth.length=PowerOfTwoApproximation.depth (roundingTolerance delta))
    (bits : Fin (wordWidth (scheduledContext A C K j delta failure z v)) → Bool) :
    TreeFraction.val (output (input (scheduledContext A C K j delta failure z v)
      (degree,depth) bits))=RootedComputedEstimator.estimate A C K j hK hW delta failure z v
        (scheduledEquiv A C K j delta failure z v bits) := by
  sorry

end
end ContingencyTables.RootedEstimatorWordProgram

end OAI
end
