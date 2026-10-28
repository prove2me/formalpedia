-- Prove2me | Theorems.Thm_OAI_MetricKMedian_Preparation_distant_assignments_s35
-- name    : OAI.MetricKMedian.Preparation.distant_assignments_s35
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T10:38:47.443353+00:00
-- url     : https://prove2.me/theorems/7dbc9134-f3de-4304-a139-477b51475ad3
-- title:
--   OAI.MetricKMedian.Preparation.distant_assignments_s35: intermediate lemma from OpenAI, The approximation threshold for metric k-median (result family 125)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.MetricKMedian.main_finite_work`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The approximation threshold for metric k-median (result family 125)*, OpenAI Math Release, September 24, 2026, result family 125, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.MetricKMedian.Preparation`, with `open Finset SupplierStars`):
--
--   ```lean
--   theorem distant_assignments_s35 (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
--       (V : T → ℝ) {M δ g γ B v p₀ α β : ℝ} {Δ : ℕ}
--       (G : BundleGeometry F y s i V M δ)
--       (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
--       (hy : ∀ a, 0 ≤ y a) (hδ : 0 < δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
--       (hg : 0 < g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
--       (hp₀ : 0 < p₀) (hp : ∀ t, p₀ ≤ G.p t) (hα : 0 ≤ α) (hα1 : α < 1)
--       (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
--       (hms : ∑ a ∈ F t, y a=1) (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
--       (hV : V t ≤ v) (R : ℝ) (hDα : dist j (s t) ≤ α*R)
--       (hmax : ∀ a ∈ F t, dist (s t) (i a) ≤ R)
--       (hmin : ∀ a ∉ F t, R ≤ dist (s t) (i a))
--       (hDβ : 0 < G.c t → dist j (s t) ≤ β*G.L t) :
--       ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
--         (∀ z, 0 < (L.ν.joint L.κ).weight z →
--           (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
--         (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
--           (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
--           farFactor δ p₀ α β γ*v
--   ```
--
--   **Definitions.** The statement is written with `OAI.MetricKMedian.FiniteLaw.expect` and `OAI.MetricKMedian.FiniteLaw` (definitions bundle `OAIQ035K004` of this split); `OAI.MetricKMedian.Preparation.BundleGeometry`, `OAI.MetricKMedian.Preparation.Physical`, `OAI.MetricKMedian.Preparation.farFactor`, `OAI.MetricKMedian.Preparation.SupplierStars.Star`, `OAI.MetricKMedian.Preparation.SupplierStars.targets` and `OAI.MetricKMedian.Preparation.SupplierStars.weight` (definitions bundle `OAIQ035K010` of this split); `OAI.MetricKMedian.FiniteLaw.joint` (definitions bundle `OAIQ035K016` of this split); `OAI.MetricKMedian.Preparation.SupplierStars.flag` (definitions bundle `OAIQ035K024` of this split); `OAI.MetricKMedian.Preparation.CoupledLaw` (definitions bundle `OAIQ035K025` of this split); `OAI.MetricKMedian.Preparation.physicalOpen` (definitions bundle `OAIQ035K036` of this split).
--
--   **Used by.** The proof of `OAI.MetricKMedian.Preparation.client_assignments_s35` of this split imports it.
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
section
namespace MetricKMedian.Preparation
open Finset SupplierStars
attribute [instance] CoupledLaw.finite
variable {I T X : Type} [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]
  [PseudoMetricSpace X]

theorem distant_assignments_s35 (F : T → Finset I) (y : I → ℝ) (s : T → X) (i : I → X)
    (V : T → ℝ) {M δ g γ B v p₀ α β : ℝ} {Δ : ℕ}
    (G : BundleGeometry F y s i V M δ)
    (L : CoupledLaw (targets G.A) flag (weight y G.P G.A G.c γ) G.P y G.p G.c g γ B Δ)
    (hy : ∀ a, 0 ≤ y a) (hδ : 0 < δ) (hβ : 0 ≤ β) (hsep : β+δ < 1)
    (hg : 0 < g) (hγ : 0 ≤ γ) (hunit : g*(Δ:ℝ)=1)
    (hp₀ : 0 < p₀) (hp : ∀ t, p₀ ≤ G.p t) (hα : 0 ≤ α) (hα1 : α < 1)
    (j : X) (t : T) (Fj : Finset I) (hmj : ∑ a ∈ Fj, y a=1)
    (hms : ∑ a ∈ F t, y a=1) (hvj : ∑ a ∈ Fj, y a*dist j (i a)=v)
    (hV : V t ≤ v) (R : ℝ) (hDα : dist j (s t) ≤ α*R)
    (hmax : ∀ a ∈ F t, dist (s t) (i a) ≤ R)
    (hmin : ∀ a ∉ F t, R ≤ dist (s t) (i a))
    (hDβ : 0 < G.c t → dist j (s t) ≤ β*G.L t) :
    ∃ r : (L.Ω × (T → Finset I)) → Physical I T → ℝ,
      (∀ z, 0 < (L.ν.joint L.κ).weight z →
        (∀ a, 0 ≤ r z a ∧ r z a ≤ physicalOpen L z a) ∧ (∑ a, r z a)=1) ∧
      (L.ν.joint L.κ).expect (fun z => ∑ a, r z a*
        (Sum.elim (fun a => dist j (i a)) (fun ti => dist j (i ti.2)) a)) ≤
        farFactor δ p₀ α β γ*v := by
  sorry

end MetricKMedian.Preparation
end
end

end OAI
end
