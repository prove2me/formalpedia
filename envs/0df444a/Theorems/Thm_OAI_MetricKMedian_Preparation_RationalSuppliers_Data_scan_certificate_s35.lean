-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_RationalSuppliers_Data_scan_certificate_s35
-- name    : OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_certificate_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:45:35.779045+00:00
-- url     : https://prove2.me/theorems/d6857446-399e-423a-9de5-7fa2d7b64a0d
-- title:
--   OAI.MetricKMedian.Preparation.RationalSuppliers.Data.scan_certificate_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation.RationalSuppliers.Data`, with `open Finset SupplierStars`):
--
--   ```lean
--   theorem scan_certificate_s35 {X : Type} [PseudoMetricSpace X]
--       (hτ : τ<1) (hj : 0<j)
--       (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
--       (i : Fin f → X) (client : Fin j → X)
--       (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
--       (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
--       (B : ℚ) (ns : List (Fin (f+n*f) → ℕ)) (n₀ : Physical (Fin f) (Fin n) → ℕ)
--       (N : Fin (f+n*f) → ℕ) (hN : N∈ns)
--       (heq : ∀ a, N a=n₀ (physicalIndex a))
--       (hcap : ∀ a, n₀ a ≤ qR.Δ)
--       (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(n₀ a:ℝ))
--       (hB : (∑ a, (qR.g:ℝ)*(n₀ a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
--       (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
--       (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(n₀ a:ℝ)) ∧
--         (∑ a, r c a)=1) :
--       ∃ O : Finset (Fin f), qR.roundList df dc (original (f:=f) (n:=n)) ns B=some O ∧ O.Nonempty ∧
--         (O.card:ℝ) ≤ (B:ℝ) ∧
--         (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
--           (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a))
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.Completion.Rational.score` (definitions bundle `OAIQ035K002` of this split); `OAI.MetricKMedian.Preparation.Physical`, `OAI.MetricKMedian.Preparation.RationalSuppliers.original` and `OAI.MetricKMedian.Preparation.RationalSuppliers.physicalIndex` (definitions bundle `OAIQ035K010` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters.allowance` (definitions bundle `OAIQ035K029` of this split); `OAI.MetricKMedian.FixedBatch.RationalParameters.roundList` (definitions bundle `OAIQ035K047` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K047

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Preparation.RationalSuppliers
open Finset SupplierStars

namespace Data
variable {f n j : ℕ} {τ : ℝ} (D : Data f n) (qR : FixedBatch.RationalParameters τ)

theorem scan_certificate_s35 {X : Type} [PseudoMetricSpace X]
    (hτ : τ<1) (hj : 0<j)
    (df : Fin f → Fin f → ℚ) (dc : Fin j → Fin f → ℚ)
    (i : Fin f → X) (client : Fin j → X)
    (hdf : ∀ a b, dist (i a) (i b)=(df a b:ℝ))
    (hdc : ∀ c a, dist (client c) (i a)=(dc c a:ℝ))
    (B : ℚ) (ns : List (Fin (f+n*f) → ℕ)) (n₀ : Physical (Fin f) (Fin n) → ℕ)
    (N : Fin (f+n*f) → ℕ) (hN : N∈ns)
    (heq : ∀ a, N a=n₀ (physicalIndex a))
    (hcap : ∀ a, n₀ a ≤ qR.Δ)
    (hm : 1 ≤ ∑ a, (qR.g:ℝ)*(n₀ a:ℝ))
    (hB : (∑ a, (qR.g:ℝ)*(n₀ a:ℝ))+(qR.allowance:ℝ) ≤ (B:ℝ))
    (r : Fin j → Physical (Fin f) (Fin n) → ℝ)
    (hr : ∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ (qR.g:ℝ)*(n₀ a:ℝ)) ∧
      (∑ a, r c a)=1) :
    ∃ O : Finset (Fin f), qR.roundList df dc (original (f:=f) (n:=n)) ns B=some O ∧ O.Nonempty ∧
      (O.card:ℝ) ≤ (B:ℝ) ∧
      (Completion.Rational.score dc O:ℝ) ≤ ((1+2/Real.exp 1+τ)/(1-τ))*
        (∑ c,∑ a, r c a*dist (client c) (Sum.elim i (fun ti => i ti.2) a)) := by
  sorry

end Data
end MetricKMedian.Preparation.RationalSuppliers
end

end OAI
end
