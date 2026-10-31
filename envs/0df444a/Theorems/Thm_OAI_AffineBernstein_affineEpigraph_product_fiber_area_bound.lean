-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_product_fiber_area_bound
-- name    : OAI.AffineBernstein.affineEpigraph_product_fiber_area_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:05:17.353414+00:00
-- url     : https://prove2.me/theorems/dc58ebbb-036f-4e7e-a242-6f0c60060fed
-- title:
--   OAI.AffineBernstein.affineEpigraph_product_fiber_area_bound: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_product_fiber_area_bound` of [lean/OAI/Analysis/AffineBernstein/ActualProductBounds.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualProductBounds.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open scoped Matrix`):
--
--   ```lean
--   theorem affineEpigraph_product_fiber_area_bound {n k m : ℕ} (hm : 1 ≤ m)
--       {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
--       {D : Set (Space k)} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0:Space m) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D) {M : ℝ}
--       (hbound : ∀ s ∈ Q, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) :
--       let H := fun q : Space k × Space m =>
--         homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
--         ENNReal.ofReal (tubeAngularDensity H (q.1,q.2) (EuclideanSpace.basisFun (Fin m) ℝ))
--         ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) ≤
--         ((m:ℝ≥0∞)^2 * volume (Metric.closedBall (0:Space m) (M+1))) * volume Q
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport` and `OAI.AffineBernstein.tubeAngularDensity` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proofs of `OAI.AffineBernstein.normalized_model_positive_log_mass` and `OAI.AffineBernstein.normalized_model_uniform_actual_sigma` of this split import it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/ActualProductBounds.lean (declaration OAI.AffineBernstein.affineEpigraph_product_fiber_area_bound)

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

theorem affineEpigraph_product_fiber_area_bound {n k m : ℕ} (hm : 1 ≤ m)
    {Ω : Set (Space n)} (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (Space k × Space m) ≃L[ℝ] (Space n × ℝ))
    {D : Set (Space k)} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:Space m) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {Q : Set (Space k)} (hQ : MeasurableSet Q) (hQD : Q ⊆ D) {M : ℝ}
    (hbound : ∀ s ∈ Q, ∀ y : Space m, (s,y) ∈ affineEpigraphPullback Ω u a L → ‖y‖ ≤ M) :
    let H := fun q : Space k × Space m =>
      homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    (∫⁻ q : Space k × Metric.sphere (0:Space m) 1,
      ENNReal.ofReal (tubeAngularDensity H (q.1,q.2) (EuclideanSpace.basisFun (Fin m) ℝ))
      ∂(volume.restrict Q).prod (volume : Measure (Space m)).toSphere) ≤
      ((m:ℝ≥0∞)^2 * volume (Metric.closedBall (0:Space m) (M+1))) * volume Q := by
  sorry

end AffineBernstein

end

end OAI
end
