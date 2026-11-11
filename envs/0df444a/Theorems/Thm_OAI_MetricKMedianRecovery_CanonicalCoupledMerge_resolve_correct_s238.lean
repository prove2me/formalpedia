-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_resolve_correct_s238
-- name    : OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:52:39.10979+00:00
-- url     : https://prove2.me/theorems/43864cc4-1844-45de-949a-ac899f009c4a
-- title:
--   OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledResolve.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledResolve.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalCoupledMerge`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing`):
--
--   ```lean
--   lemma resolve_correct_s238 (loc : Fin d → V) (distance : V → Fin d → ℚ)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
--       (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision q n k key : ℕ)
--       (B : Finset (Label V)) (lam : ℚ) (P : List (List (Label V)))
--       (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N) (hB : Before key B) (hkey : key<3*(q+1))
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
--       (hdis : Disjoint (F.image original) B) (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
--       (hlamUpper : (lam:ℝ)≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
--       (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ))
--       (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
--       (R : CanonicalMergeCrossing.Result (Label V))
--       (hR : R.Correct (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam eta q n k) :
--       (resolve loc distance F v M N precision q n k key B lam P R).Correct loc F v eta lo hi q n k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Result` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.PhaseHistoryTransfer.after` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.metric` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.PhaseMergeInvariant.PrefixData` and `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Result.Correct` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238K017` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Before` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve` (definitions bundle `Q238K027` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Outcome.Correct` (definitions bundle `Q238K031` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.step_correct_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/CoupledResolve.lean (declaration OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct)

import Mathlib
import Definitions.Def_Q238K031

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge

section
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge CanonicalLengthView
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma resolve_correct_s238 (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (v M : ℚ) (eta lo hi : ℝ) (N precision q n k key : ℕ)
    (B : Finset (Label V)) (lam : ℚ) (P : List (List (Label V)))
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N) (hB : Before key B) (hkey : key<3*(q+1))
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlam : (0:ℝ)<(lam:ℝ)) (heta : 0≤eta)
    (hdis : Disjoint (F.image original) B) (hl : lo≤(lam:ℝ)) (hu : (lam:ℝ)≤hi)
    (hlamUpper : (lam:ℝ)≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ))
    (hp : PrefixData (fun j=>original (loc j)) (F.image original) B v lam eta q P)
    (R : CanonicalMergeCrossing.Result (Label V))
    (hR : R.Correct (fun j=>original (loc j)) (F.image original) B (after ∅ P) v lam eta q n k) :
    (resolve loc distance F v M N precision q n k key B lam P R).Correct loc F v eta lo hi q n k := by
  sorry

end

open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing RationalLeaves PhaseMergeInvariant PhaseCoupledMerge
attribute [local instance] RationalLeaves.metric

end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end
