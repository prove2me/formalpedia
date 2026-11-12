-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_transition_valid_s238r
-- name    : OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:54:24.438349+00:00
-- url     : https://prove2.me/theorems/82e2d290-595b-4c9a-9328-68b33dea54ad
-- title:
--   OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid` of [lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopInvariant.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopInvariant.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalCoupledMerge`, with `open RationalLeaves RationalHeight`):
--
--   ```lean
--   lemma transition_valid_s238r (loc : Fin d→V) (distance : V→Fin d→ℚ)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
--       (v M : ℚ) (eta lo hi : ℝ) (N precision total k H p : ℕ)
--       (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
--       (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
--       (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
--       (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) (hfar : Height (20*N*M) H)
--       (f : Frame V) (hf : f.Valid loc F v eta lo hi total k (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p) :
--       (transition loc distance F v M N precision k f).Valid loc F v eta lo hi total k
--         (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.CanonicalLengthSearch.heightBudget` and `OAI.MetricKMedianRecovery.RationalHeight.Height` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame` (definitions bundle `Q238L025` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.Frame.Valid` (definitions bundle `Q238L031` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCoupledLoop.run_initial_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Machines/LoopInvariant.lean (declaration OAI.MetricKMedianRecovery.CanonicalCoupledMerge.transition_valid)

import Mathlib
import Definitions.Def_Q238L031

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open RationalLeaves RationalHeight
variable {V : Type*} [LinearOrder V] {d : ℕ}

variable [PseudoMetricSpace V]
attribute [local instance] RationalLeaves.metric

lemma transition_valid_s238r (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v M : ℚ) (eta lo hi : ℝ) (N precision total k H p : ℕ)
    (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<v) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hhi : hi≤8*N*(M:ℝ)) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) (hfar : Height (20*N*M) H)
    (f : Frame V) (hf : f.Valid loc F v eta lo hi total k (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p) :
    (transition loc distance F v M N precision k f).Valid loc F v eta lo hi total k
      (CanonicalLengthSearch.heightBudget (20*N*M) precision H) p := by
  sorry
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end
