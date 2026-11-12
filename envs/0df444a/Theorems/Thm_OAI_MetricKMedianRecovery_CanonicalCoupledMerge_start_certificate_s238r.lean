-- Prove2me | Theorems.Thm_OAI_MetricKMedianRecovery_CanonicalCoupledMerge_start_certificate_s238r
-- name    : OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238r
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T11:39:58.720205+00:00
-- url     : https://prove2.me/theorems/d2b421a2-afba-4dd1-bd03-171521bf1175
-- title:
--   OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate_s238r: intermediate lemma from OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedianRecovery.global_application`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate` of [lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedianRecovery.CanonicalCoupledMerge`, with `open PhaseOriginalLedger HistoryPhaseBound`):
--
--   ```lean
--   lemma start_certificate_s238r (loc : Fin d→V) (distance : V→Fin d→ℚ)
--       (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
--       (v lo M : ℚ) (eta : ℝ) (N precision k : ℕ)
--       (hd : 0<d) (hdN : d≤N) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
--       (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
--       (hlohi : lo≤8*(d:ℚ)*M) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
--       (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
--       let total := limit v ((M:ℝ)+8*(d:ℝ)*M)+1
--       let S := (start loc distance F v lo M N precision total k).project
--       LowCertificate loc F S v lo k ∨ NormalCertificate loc F S v lo (8*(d:ℝ)*M) eta total k
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedianRecovery.HistoryPhaseBound.limit` (definitions bundle `Q238L004` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.LowCertificate` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.NormalCertificate` (definitions bundle `Q238L010` of this split); `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start` and `OAI.MetricKMedianRecovery.CanonicalCoupledMerge.StartOutput.project` (definitions bundle `Q238L026` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedianRecovery.BitMachine.BinaryCanonicalSurplus.produce_s238r` of this split imports it.
-- source:
--   OpenAI, Single-Exponential Recovery and Bounded-Price Strictness for Metric k-Median, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Single-Exponential-Recovery-and-Bounded-Price-Strictness-for-Metric-k-Median-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/KMedianRecovery/Recovery/InitialProject.lean (declaration OAI.MetricKMedianRecovery.CanonicalCoupledMerge.start_certificate)

import Mathlib
import Definitions.Def_Q238L026

section

attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.CanonicalCoupledMerge
open PhaseOriginalLedger HistoryPhaseBound
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {d : ℕ}
lemma start_certificate_s238r (loc : Fin d→V) (distance : V→Fin d→ℚ)
    (hmetric : ∀ x j,(distance x j:ℝ)=dist x (loc j)) (F : Finset V)
    (v lo M : ℚ) (eta : ℝ) (N precision k : ℕ)
    (hd : 0<d) (hdN : d≤N) (hk : 2≤k) (hF : F.Nonempty) (hM : 0<M) (hN : 3≤N)
    (hv : (0:ℝ)<(v:ℝ)) (hv1 : (v:ℝ)<1/6) (hlo : 0<lo) (heta : 0≤eta)
    (hlohi : lo≤8*(d:ℚ)*M) (hprecision : (1/(2:ℚ)^precision:ℚ)≤eta)
    (hfar : ∀ i∈F,∀ j,1≤dist i (loc j)) (hdiam : ∀ i∈F,∀ j,dist i (loc j)≤(M:ℝ)) :
    let total := limit v ((M:ℝ)+8*(d:ℝ)*M)+1
    let S := (start loc distance F v lo M N precision total k).project
    LowCertificate loc F S v lo k ∨ NormalCertificate loc F S v lo (8*(d:ℝ)*M) eta total k := by
  sorry
end MetricKMedianRecovery.CanonicalCoupledMerge

end OAI
end
