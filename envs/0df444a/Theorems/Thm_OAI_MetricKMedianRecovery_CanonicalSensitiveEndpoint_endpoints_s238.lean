-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalSensitiveEndpoint_endpoints_s238
-- name    : OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-10T23:48:56.490491+00:00
-- url     : https://prove2.me/theorems/72ac9e1a-ea32-4e28-9d41-5f713d7b6327
-- title:
--   OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints_s238: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/LengthSearch.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/LengthSearch.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint`, with `open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing`):
--
--   ```lean
--   lemma endpoints_s238 (loc : Fin d → V) (distance : V → Fin d → ℚ)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
--       (F : Finset V) (B Q : Finset (Label V)) (v lam eta M : ℝ)
--       (q n k key N : ℕ) (b : ℚ) (H G : List (Label V))
--       (T U : List (List (Label V))) (J : Plan (Label V))
--       (hF : F.Nonempty) (hB : Before key B) (hQ : Q⊆F.image original∪B)
--       (hdis : Disjoint (F.image original) B) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
--       (hM : 0<M) (hN : 3≤N) (hlamUpper : lam≤8*N*M) (hb : 20*N*M≤(b:ℝ))
--       (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M)
--       (hrow : ∀ x∈F.image original,bidRow (fun j=>original (loc j)) (1-3*v) ((1+v^2)^q) Q x≤lam)
--       (hH : Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta H)
--       (hG : Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta G)
--       (hT : Runs (fun j=>original (loc j)) (F.image original) B (Q∪H.toFinset) v lam (q+1) n T)
--       (hU : Runs (fun j=>original (loc j)) (F.image original) B (Q∪G.toFinset) v lam (q+1) n U)
--       (hacc : accepts (rows distance) (F.image original) H G J)
--       (hs : Sandwich k (finalCount (F.image original) Q H T) (finalCount (F.image original) Q G U)) :
--       EndpointSpec loc F B Q v lam eta q n k key b H T U J
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.bidRow` (definitions bundle `Q238K000` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Label` (definitions bundle `Q238K002` of this split); `OAI.MetricKMedianRecovery.CanonicalLengthView.Plan` (definitions bundle `Q238K003` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.finalCount` and `OAI.MetricKMedianRecovery.PhaseCountCrossing.Sandwich` (definitions bundle `Q238K004` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.metric` (definitions bundle `Q238K010` of this split); `OAI.MetricKMedianRecovery.CanonicalMergeCrossing.Runs` and `OAI.MetricKMedianRecovery.PhaseMergeRefinement.Good` (definitions bundle `Q238K014` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.original` (definitions bundle `Q238K017` of this split); `OAI.MetricKMedianRecovery.RationalLeaves.Before` and `OAI.MetricKMedianRecovery.RationalLeaves.rows` (definitions bundle `Q238K021` of this split); `OAI.MetricKMedianRecovery.CanonicalLengthView.accepts` (definitions bundle `Q238K022` of this split); `OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.EndpointSpec` (definitions bundle `Q238K027` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.resolve_correct_s238` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/LengthSearch.lean (declaration OAI.MetricKMedianRecovery.CanonicalSensitiveEndpoint.endpoints)

import Mathlib
import Definitions.Def_Q238K027

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype _root_.OAI.MetricKMedianRecovery.RationalLeaves.labelLinearOrder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalSensitiveEndpoint
open PhaseSequence PhaseHistoryTransfer PhaseMergeCompletion PhaseMergeRefinement PhaseCountCrossing
  CanonicalMergeCrossing CanonicalLengthView RationalLeaves
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V] {d : ℕ}
attribute [local instance] RationalLeaves.metric

lemma endpoints_s238 (loc : Fin d → V) (distance : V → Fin d → ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j))
    (F : Finset V) (B Q : Finset (Label V)) (v lam eta M : ℝ)
    (q n k key N : ℕ) (b : ℚ) (H G : List (Label V))
    (T U : List (List (Label V))) (J : Plan (Label V))
    (hF : F.Nonempty) (hB : Before key B) (hQ : Q⊆F.image original∪B)
    (hdis : Disjoint (F.image original) B) (hv : 0<v) (hv1 : v<1/6) (hlam : 0<lam)
    (hM : 0<M) (hN : 3≤N) (hlamUpper : lam≤8*N*M) (hb : 20*N*M≤(b:ℝ))
    (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤M)
    (hrow : ∀ x∈F.image original,bidRow (fun j=>original (loc j)) (1-3*v) ((1+v^2)^q) Q x≤lam)
    (hH : Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta H)
    (hG : Good (fun j=>original (loc j)) (F.image original) B Q v ((1+v^2)^q) lam eta G)
    (hT : Runs (fun j=>original (loc j)) (F.image original) B (Q∪H.toFinset) v lam (q+1) n T)
    (hU : Runs (fun j=>original (loc j)) (F.image original) B (Q∪G.toFinset) v lam (q+1) n U)
    (hacc : accepts (rows distance) (F.image original) H G J)
    (hs : Sandwich k (finalCount (F.image original) Q H T) (finalCount (F.image original) Q G U)) :
    EndpointSpec loc F B Q v lam eta q n k key b H T U J := by
  sorry

end MetricKMedianRecovery.CanonicalSensitiveEndpoint

end OAI
end
