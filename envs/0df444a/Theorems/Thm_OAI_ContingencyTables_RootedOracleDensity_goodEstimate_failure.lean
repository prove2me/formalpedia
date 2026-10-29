-- Prove2me | Theorems.Thm_OAI_ContingencyTables_RootedOracleDensity_goodEstimate_failure
-- name    : OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-29T04:03:56.037599+00:00
-- url     : https://prove2.me/theorems/6ef91d0d-c3c5-4edb-8fb7-465fe303881b
-- title:
--   OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure: intermediate lemma from OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ContingencyTables.boundedSampling`, `OAI.ContingencyTables.counting` and `OAI.ContingencyTables.exactSampling`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Sampling and counting contingency tables with arbitrary margins (result family 115)*, OpenAI Math Release, September 24, 2026, result family 115, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure` of [lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorConfidence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorConfidence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ContingencyTables.RootedOracleDensity`, with `open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess`, `open CommonBasesFPRAS FiniteIndependentAverages`, `open CompanionOracleDensity`, `open scoped BigOperators Classical`):
--
--   ```lean
--   theorem goodEstimate_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
--       (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
--       (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
--       (delta failure : ℚ) (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
--       (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
--       (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
--       (v : Grid (I := Fin (dimension A)) K) :
--       uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
--         if ¬GoodEstimate A R C z K hK hW j delta failure v draws then (1:ℝ) else 0) ≤ (failure:ℝ)/4
--   ```
--
--   **Definitions.** The statement is written with `OAI.CommonBasesFPRAS.uniformAverage` and `OAI.ContingencyTables.BalancedBox.InBox` (definitions bundle `OAIQ089A000` of this split); `OAI.ContingencyTables.CompanionFactorialApplication.Instance`, `OAI.ContingencyTables.CompanionFactorialApplication.View`, `OAI.ContingencyTables.CompanionFactorialApplication.bounds`, `OAI.ContingencyTables.CompanionOracleDensity.CorrectionBlock`, `OAI.ContingencyTables.CompanionOracleDensity.EstimatorInput`, `OAI.ContingencyTables.CompanionOracleDensity.RatioBlock`, `OAI.ContingencyTables.CompanionOracleDensity.RatioWords`, `OAI.ContingencyTables.CompanionOracleDensity.binWidth`, `OAI.ContingencyTables.CompanionOracleDensity.correctionTheta`, `OAI.ContingencyTables.CompanionOracleDensity.dimension`, `OAI.ContingencyTables.CompanionOracleDensity.offsetAccuracy`, `OAI.ContingencyTables.CompanionOracleDensity.oracleIntegerBits`, `OAI.ContingencyTables.CompanionOracleDensity.oracleStepBits`, `OAI.ContingencyTables.CompanionOracleDensity.oracleTime`, `OAI.ContingencyTables.CompanionOracleDensity.rationalHeight`, `OAI.ContingencyTables.CompanionOracleDensity.sampleCount`, `OAI.ContingencyTables.GridBoundary.Grid` and `OAI.ContingencyTables.RootedCompletion.Selection` (definitions bundle `OAIQ089A001` of this split); `OAI.ContingencyTables.PublishedInputs.FiniteBoxPrekopaLeindler` and `OAI.ContingencyTables.PublishedInputs.FiniteCheeger` (definitions bundle `OAIQ089A004` of this split); `OAI.ContingencyTables.RootedOracleDensity.GoodEstimate` (definitions bundle `OAIQ089A009` of this split).
--
--   **Used by.** The proofs of `OAI.ContingencyTables.ComputedCountingZero.zero_success`, `OAI.ContingencyTables.RootedPlainTrial.trial_failure` and `OAI.ContingencyTables.RootedTraceWords.arithmetic_recorded_event_bound` of this split import it.
-- source:
--   OpenAI, Sampling and counting contingency tables with arbitrary margins (result family 115), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 115; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/ContingencyTables/Rooted/RootedEstimatorConfidence.lean (declaration OAI.ContingencyTables.RootedOracleDensity.goodEstimate_failure)

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ089A009

section

attribute [-instance] _root_.OAI.ContingencyTables.ExcessContextProfiles.validAssignmentsFintype _root_.OAI.ContingencyTables.IntegerWeightedTransport.excessAssignmentsFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.paperStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.physicalStatesFintype _root_.OAI.ContingencyTables.SmallGraphProfiles.profilesFintype _root_.OAI.MatchingFPRAS.OnlineControl.instFintypeLabel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ContingencyTables.RootedOracleDensity

open CompanionFactorialApplication ForestAssignmentSplit GridBoundary ResidualMixture FirstSuccess
open CommonBasesFPRAS FiniteIndependentAverages
open CompanionOracleDensity
open scoped BigOperators Classical

noncomputable section

variable {I J : Type*} [Fintype I] [Fintype J]

theorem goodEstimate_failure (A : Instance I J) (R : RootedCompletion.Selection A.T) (C : ℕ) (hC : 0 < C) (z : View A → ℕ)
    (hz : BalancedBox.InBox (bounds A) z) (K : ℕ) (hK : 1 ≤ K) (hW : 100*A.d*K ≤ A.W)
    (hB : (K:ℝ)=binWidth A C) (j : ℕ) (hj : j ≤ rationalHeight A C)
    (delta failure : ℚ) (hd0 : 0 < delta) (hd1 : delta < 1) (hf : 0 < failure)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (dimension A))
    (hCheeger : PublishedInputs.FiniteCheeger (Grid (I := Fin (dimension A)) K))
    (v : Grid (I := Fin (dimension A)) K) :
    uniformAverage (fun draws : EstimatorInput A C K j delta failure =>
      if ¬GoodEstimate A R C z K hK hW j delta failure v draws then (1:ℝ) else 0) ≤ (failure:ℝ)/4 := by
  sorry

end

end ContingencyTables.RootedOracleDensity

end OAI
end
