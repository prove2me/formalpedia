-- Prove2me | Theorems.Thm_OAI_AffineBernstein_complete_affineMaximal_uniform_spherical_cap_bound
-- name    : OAI.AffineBernstein.complete_affineMaximal_uniform_spherical_cap_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:10:19.574391+00:00
-- url     : https://prove2.me/theorems/2491a4ed-b0de-42c8-90df-ef53e5536102
-- title:
--   OAI.AffineBernstein.complete_affineMaximal_uniform_spherical_cap_bound: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.complete_affineMaximal_uniform_spherical_cap_bound` of [lean/OAI/Analysis/AffineBernstein/CompleteSphericalCaps.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/CompleteSphericalCaps.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open intervalIntegral`, `open scoped Pointwise`, `open Filter`, `open scoped Topology`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem complete_affineMaximal_uniform_spherical_cap_bound {n : ℕ}
--       (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
--       (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ)
--       (ℓ : S →L[ℝ] ℝ) (o : S × E) {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r)
--       (hR : 0 ≤ R) (t₁ : ℝ) (hogap : ℓ o.1 < t₁+ε) :
--       ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
--         ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
--         (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
--         ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--           {B : Set S}, IsOpen B → (∀ s ∈ B, ℓ s ≤ t₁+ε) →
--         (∀ s ∈ B, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
--         (∀ p ∈ affineEpigraphPullback Ω u a L, ℓ p.1 ≤ t₁+ε → ‖p‖ ≤ R) →
--         Metric.closedBall o r ⊆ affineEpigraphPullback Ω u a L →
--         ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ B → (∀ s ∈ Q, ℓ s ≤ t₁-ε) →
--         let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--         let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
--         (∫⁻ q : S × Metric.sphere (0:E) 1, ENNReal.ofReal
--           ((Real.rpow (tubeBaseMatrix H (q.1,q.2) bS.toBasis).det δ *
--             Real.rpow (tubeAngularDensity H (q.1,q.2) bRef) (1-δ)) *
--             (‖supportConormal H (q.1,q.2)‖ *
--               inverseMatrixPair (tubeBaseMatrix H (q.1,q.2) bS.toBasis)
--                 (fun i => ℓ (bS i)) (fun i => ℓ (bS i))))
--           ∂(volume.restrict Q).prod volume.toSphere) ≤ ENNReal.ofReal C
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.inverseMatrixPair`, `OAI.AffineBernstein.supportConormal`, `OAI.AffineBernstein.tubeAngularDensity` and `OAI.AffineBernstein.tubeBaseMatrix` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.AffineMaximalOn`, `OAI.AffineBernstein.EuclideanGraphComplete`, `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.normalized_model_uniform_actual_sigma` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/CompleteSphericalCaps.lean (declaration OAI.AffineBernstein.complete_affineMaximal_uniform_spherical_cap_bound)

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
open intervalIntegral
open scoped Pointwise
open Filter
open scoped Topology
open Filter
open scoped Topology

variable {S E F : Type*} [NormedAddCommGroup S] [InnerProductSpace ℝ S]
  [FiniteDimensional ℝ S] [MeasurableSpace S] [BorelSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Nontrivial E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem complete_affineMaximal_uniform_spherical_cap_bound {n : ℕ}
    (bS : OrthonormalBasis ι ℝ S) (bF : OrthonormalBasis κ ℝ F)
    (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (e : Fin n ≃ ι ⊕ κ)
    (ℓ : S →L[ℝ] ℝ) (o : S × E) {ε r R : ℝ} (hε : 0 < ε) (hr : 0 < r)
    (hR : 0 ≤ R) (t₁ : ℝ) (hogap : ℓ o.1 < t₁+ε) :
    ∃ C > 0, ∀ {Ω : Set (Space n)}, IsOpen Ω → Ω.Nonempty → Convex ℝ Ω →
      ∀ {u : Space n → ℝ}, ContDiffOn ℝ ∞ u Ω →
      (∀ x ∈ Ω, (hessian u x).PosDef) → AffineMaximalOn Ω u → EuclideanGraphComplete Ω u →
      ∀ (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
        {B : Set S}, IsOpen B → (∀ s ∈ B, ℓ s ≤ t₁+ε) →
      (∀ s ∈ B, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L}) →
      (∀ p ∈ affineEpigraphPullback Ω u a L, ℓ p.1 ≤ t₁+ε → ‖p‖ ≤ R) →
      Metric.closedBall o r ⊆ affineEpigraphPullback Ω u a L →
      ∀ {Q : Set S}, MeasurableSet Q → Q ⊆ B → (∀ s ∈ Q, ℓ s ≤ t₁-ε) →
      let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
      let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
      (∫⁻ q : S × Metric.sphere (0:E) 1, ENNReal.ofReal
        ((Real.rpow (tubeBaseMatrix H (q.1,q.2) bS.toBasis).det δ *
          Real.rpow (tubeAngularDensity H (q.1,q.2) bRef) (1-δ)) *
          (‖supportConormal H (q.1,q.2)‖ *
            inverseMatrixPair (tubeBaseMatrix H (q.1,q.2) bS.toBasis)
              (fun i => ℓ (bS i)) (fun i => ℓ (bS i))))
        ∂(volume.restrict Q).prod volume.toSphere) ≤ ENNReal.ofReal C := by
  sorry

end AffineBernstein

end

end OAI
end
