-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_selected_preparation_outcome_s35
-- name    : OAI.MetricKMedian.Preparation.selected_preparation_outcome_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:39:28.313872+00:00
-- url     : https://prove2.me/theorems/4307045f-91ec-4a79-aac3-4d866e2cbbe3
-- title:
--   OAI.MetricKMedian.Preparation.selected_preparation_outcome_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation`, with `open Finset SupplierStars`):
--
--   ```lean
--   theorem selected_preparation_outcome_s35 (F : T → Finset I) (Fj : J → Finset I) (y : I → ℝ)
--       (s : T → X) (j : J → X) (i : I → X) (V : T → ℝ) (v : J → ℝ) (rep : J → T)
--       {M δ T₁ g γ : ℝ} {Δ : ℕ}
--       (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a ≤ 1)
--       (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) (hT : 0 < T₁)
--       (hθ : 1/(M*δ) ≤ 1/8) (hα : M/(δ*T₁) ≤ 1/4)
--       (hg : 0 < g) (hγ : 0 < γ) (_ : γ ≤ 1) (_ : Even Δ) (hunit : g*(Δ:ℝ)=1)
--       (hfail : failureFactor γ g < 1)
--       (hsunit : ∀ t, ∑ a ∈ F t, y a=1)
--       (hjunit : ∀ c, ∑ a ∈ Fj c, y a=1)
--       (_ : ∀ t, ∑ a ∈ F t, y a*dist (s t) (i a)=V t)
--       (hjcost : ∀ c, ∑ a ∈ Fj c, y a*dist (j c) (i a)=v c)
--       (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, dist (s t) (i a) ≤ dist (s t) (i b))
--       (_ : ∀ t u, t ≠ u → M*max (V t) (V u) < dist (s t) (s u))
--       (hrepV : ∀ c, V (rep c) ≤ v c) (hrepD : ∀ c, dist (j c) (s (rep c)) ≤ M*v c)
--       (G : BundleGeometry F y s i V M δ)
--       (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c
--         g γ (∑ a, y a) Δ) :
--       ∃ z : L.Ω × (T → Finset I), 0 < (L.ν.joint L.κ).weight z ∧
--       ∃ r : J → Physical I T → ℝ,
--         let n := physicalCount L z;
--         (∀ a, n a ≤ Δ) ∧
--         1 ≤ ∑ a, g*(n a:ℝ) ∧ (∑ a, g*(n a:ℝ)) ≤ (∑ a, y a)+3*g ∧
--         (∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ g*(n a:ℝ)) ∧ (∑ a, r c a)=1) ∧
--         (∑ c, ∑ a, r c a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)) ≤
--           (max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
--           (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ g)/(1-failureFactor γ g))*(∑ c, v c)
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.Preparation.BundleGeometry`, `OAI.MetricKMedian.Preparation.Physical`, `OAI.MetricKMedian.Preparation.failureFactor`, `OAI.MetricKMedian.Preparation.farFactor`, `OAI.MetricKMedian.Preparation.nearFactor`, `OAI.MetricKMedian.Preparation.SupplierStars.Star`, `OAI.MetricKMedian.Preparation.SupplierStars.targets` and `OAI.MetricKMedian.Preparation.SupplierStars.weight` (definitions bundle `OAIQ035K010` of this split); `OAI.MetricKMedian.FiniteLaw.joint` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.Preparation.SupplierStars.flag` (definitions bundle `OAIQ035K024` of this split); `OAI.MetricKMedian.Preparation.CoupledLaw` (definitions bundle `OAIQ035K025` of this split); `OAI.MetricKMedian.Preparation.physicalCount` (definitions bundle `OAIQ035K036` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.RationalUnitInput.scan_spec_s35` of this split imports it.
-- source:
--   OpenAI, The approximation threshold for metric k-median (result family 125), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 125; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Approximation-Threshold-for-Metric-k-Median-September-24-2026/main.pdf; Apache License 2.0)

import Mathlib
import Definitions.Def_OAIQ035K016
import Definitions.Def_OAIQ035K036

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T J X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [Fintype J] [Nonempty J] [PseudoMetricSpace X]

theorem selected_preparation_outcome_s35 (F : T → Finset I) (Fj : J → Finset I) (y : I → ℝ)
    (s : T → X) (j : J → X) (i : I → X) (V : T → ℝ) (v : J → ℝ) (rep : J → T)
    {M δ T₁ g γ : ℝ} {Δ : ℕ}
    (hy : ∀ a, 0 < y a) (hy1 : ∀ a, y a ≤ 1)
    (hM : 0 < M) (hδ : 0 < δ) (hδ1 : δ ≤ 1/4) (hT : 0 < T₁)
    (hθ : 1/(M*δ) ≤ 1/8) (hα : M/(δ*T₁) ≤ 1/4)
    (hg : 0 < g) (hγ : 0 < γ) (_ : γ ≤ 1) (_ : Even Δ) (hunit : g*(Δ:ℝ)=1)
    (hfail : failureFactor γ g < 1)
    (hsunit : ∀ t, ∑ a ∈ F t, y a=1)
    (hjunit : ∀ c, ∑ a ∈ Fj c, y a=1)
    (_ : ∀ t, ∑ a ∈ F t, y a*dist (s t) (i a)=V t)
    (hjcost : ∀ c, ∑ a ∈ Fj c, y a*dist (j c) (i a)=v c)
    (hnearest : ∀ t, ∀ a ∈ F t, ∀ b ∉ F t, dist (s t) (i a) ≤ dist (s t) (i b))
    (_ : ∀ t u, t ≠ u → M*max (V t) (V u) < dist (s t) (s u))
    (hrepV : ∀ c, V (rep c) ≤ v c) (hrepD : ∀ c, dist (j c) (s (rep c)) ≤ M*v c)
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c
      g γ (∑ a, y a) Δ) :
    ∃ z : L.Ω × (T → Finset I), 0 < (L.ν.joint L.κ).weight z ∧
    ∃ r : J → Physical I T → ℝ,
      let n := physicalCount L z;
      (∀ a, n a ≤ Δ) ∧
      1 ≤ ∑ a, g*(n a:ℝ) ∧ (∑ a, g*(n a:ℝ)) ≤ (∑ a, y a)+3*g ∧
      (∀ c, (∀ a, 0 ≤ r c a ∧ r c a ≤ g*(n a:ℝ)) ∧ (∑ a, r c a)=1) ∧
      (∑ c, ∑ a, r c a*dist (j c) (Sum.elim i (fun ti => i ti.2) a)) ≤
        (max (farFactor δ (1-1/(M*δ)) (M/(δ*T₁)) (M/T₁) γ)
        (nearFactor (1-1/(M*δ)) (M+(1+δ)*T₁) γ g)/(1-failureFactor γ g))*(∑ c, v c) := by
  sorry

end MetricKMedian.Preparation
end

end OAI
end
