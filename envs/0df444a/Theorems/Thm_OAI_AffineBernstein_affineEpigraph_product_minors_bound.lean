-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_product_minors_bound
-- name    : OAI.AffineBernstein.affineEpigraph_product_minors_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:05:35.653236+00:00
-- url     : https://prove2.me/theorems/e90c3f1d-2008-4487-ad9e-0d2c899cb9e2
-- title:
--   OAI.AffineBernstein.affineEpigraph_product_minors_bound: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_product_minors_bound` of [lean/OAI/Analysis/AffineBernstein/ActualProductBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualProductBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open scoped Matrix`):
--
--   ```lean
--   theorem affineEpigraph_product_minors_bound {n k m : ℕ} (hm : 1 ≤ m)
--       {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
--       {D : Set (Space k)} (hD : IsOpen D) (hcD : Convex ℝ D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0:Space m) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
--       {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
--       (hball : ∀ s ∈ Q, Metric.closedBall s r ⊆ D)
--       (hbound : ∀ s ∈ D, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M)
--       (hR : ∀ s ∈ Q, ‖s‖ ≤ R) :
--       let H := fun q : Space k × Space m =>
--         homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let B := fun q : Space k × Metric.sphere (0:Space m) 1 =>
--         tubeBaseMatrix H (q.1,q.2) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
--       (∫⁻ q, ENNReal.ofReal ((B q).det * (1+(B q)⁻¹.trace))
--         ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) ≤
--         (((k:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space k) (2*M/r+R))) *
--           (volume : Measure (Space m)).toSphere Set.univ
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport` and `OAI.AffineBernstein.tubeBaseMatrix` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.normalized_model_uniform_actual_sigma` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualProductBounds.lean (declaration OAI.AffineBernstein.affineEpigraph_product_minors_bound)

import Mathlib
import Definitions.Def_AffineBernstein
import Definitions.Def_OAIQ22Ab000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace AffineBernstein

open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
open scoped Matrix

theorem affineEpigraph_product_minors_bound {n k m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D) (hcD : Convex ℝ D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:Space m) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D)
    {r M R : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hball : ∀ s ∈ Q, Metric.closedBall s r ⊆ D)
    (hbound : ∀ s ∈ D, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M)
    (hR : ∀ s ∈ Q, ‖s‖ ≤ R) :
    let H := fun q : Space k × Space m =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let B := fun q : Space k × Metric.sphere (0:Space m) 1 =>
      tubeBaseMatrix H (q.1,q.2) (EuclideanSpace.basisFun (Fin k) ℝ).toBasis
    (∫⁻ q, ENNReal.ofReal ((B q).det * (1+(B q)⁻¹.trace))
      ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) ≤
      (((k:ℝ≥0∞)+1) * volume (Metric.closedBall (0:Space k) (2*M/r+R))) *
        (volume : Measure (Space m)).toSphere Set.univ := by
  sorry

end AffineBernstein

end

end OAI
end
