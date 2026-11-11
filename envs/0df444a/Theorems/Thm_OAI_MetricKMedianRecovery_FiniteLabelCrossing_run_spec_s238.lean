-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_FiniteLabelCrossing_run_spec_s238
-- name    : OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:30:02.435373+00:00
-- url     : https://prove2.me/theorems/260529af-091d-4db2-bfb7-139b3e2f7bb3
-- title:
--   OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteCross.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteCross.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.FiniteLabelCrossing`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing PhaseCountCrossing`):
--
--   ```lean
--    theorem run_spec_s238 (loc : Fin d → X) (distance : X → Fin d → ℚ)
--       (hmetric : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset X)
--       (v lam : ℚ) (eta : ℝ) (q n k : ℕ) (copy spare : X → X)
--       (hv : (0:ℝ)<(v:ℝ)) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
--       (hQ : Q⊆F∪B) (hdis : Disjoint F B)
--       (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i ≤ (lam:ℝ))
--       (hc : ∀ i∈F,copy i∉F∪B) (hd : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy i))
--       (hs : ∀ i∈F,spare i∉F∪PhaseMergePath.pool F B copy)
--       (he : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (spare i))
--       (H G : List X) (T U : List (List X))
--       (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H)
--       (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G)
--       (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
--       (hT : Runs loc F B (Q∪H.toFinset) v lam (q+1) n T)
--       (hU : Runs loc F B (Q∪G.toFinset) v lam (q+1) n U)
--       (hbr : Sandwich k (finalCount F Q H T) (finalCount F Q G U)) :
--       (run loc distance F Q v lam q n k copy spare H G T U).Correct loc F
--         (PhaseMergePath.pool F (PhaseMergePath.pool F B copy) spare) Q v lam eta q n k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.finalCount`, `OAI.MetricKMedianRecovery.PhaseCountCrossing.Sandwich` and `OAI.MetricKMedianRecovery.PhaseMergePath.pool` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Runs`, `OAI.MetricKMedianRecovery.PhaseSequence.Valid` and `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Result.Correct` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.FiniteLabelCrossing.run` (definitions bundle `Q238K022` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/FiniteCross.lean (declaration OAI.MetricKMedianRecovery.FiniteLabelCrossing.run_spec)

import Mathlib
import Definitions.Def_Q238K022

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.FiniteLabelCrossing
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion CanonicalMergeCrossing PhaseCountCrossing
variable {X : Type*} [LinearOrder X] {d : ℕ}

variable [PseudoMetricSpace X]
 theorem run_spec_s238 (loc : Fin d → X) (distance : X → Fin d → ℚ)
    (hmetric : ∀ f j,(distance f j:ℝ)=dist f (loc j)) (F B Q : Finset X)
    (v lam : ℚ) (eta : ℝ) (q n k : ℕ) (copy spare : X → X)
    (hv : (0:ℝ)<(v:ℝ)) (hvsmall : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
    (hQ : Q⊆F∪B) (hdis : Disjoint F B)
    (hrow : ∀ i∈F,bidRow loc (1-3*(v:ℝ)) ((1+(v:ℝ)^2)^q) Q i ≤ (lam:ℝ))
    (hc : ∀ i∈F,copy i∉F∪B) (hd : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (copy i))
    (hs : ∀ i∈F,spare i∉F∪PhaseMergePath.pool F B copy)
    (he : ∀ i∈F,∀ j,dist (loc j) i=dist (loc j) (spare i))
    (H G : List X) (T U : List (List X))
    (hH : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta H)
    (hG : Valid loc F B Q v ((1+(v:ℝ)^2)^q) lam eta G)
    (hHr : ∀ i∈H,i∈F) (hGr : ∀ i∈G,i∈F)
    (hT : Runs loc F B (Q∪H.toFinset) v lam (q+1) n T)
    (hU : Runs loc F B (Q∪G.toFinset) v lam (q+1) n U)
    (hbr : Sandwich k (finalCount F Q H T) (finalCount F Q G U)) :
    (run loc distance F Q v lam q n k copy spare H G T U).Correct loc F
      (PhaseMergePath.pool F (PhaseMergePath.pool F B copy) spare) Q v lam eta q n k := by
  sorry

end MetricKMedianRecovery.FiniteLabelCrossing

end OAI
end
