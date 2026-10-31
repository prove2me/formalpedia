-- Prove2me | Theorems.Thm_OAI_AffineBernstein_affineEpigraph_sphere_inverseArea_two_flat_lintegral
-- name    : OAI.AffineBernstein.affineEpigraph_sphere_inverseArea_two_flat_lintegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T09:05:57.99736+00:00
-- url     : https://prove2.me/theorems/1a15d5a9-d147-4d15-9a62-d9f130c9d909
-- title:
--   OAI.AffineBernstein.affineEpigraph_sphere_inverseArea_two_flat_lintegral: intermediate lemma from OpenAI, The affine Bernstein theorem in dimensions three through nine
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.AffineBernstein.affine_bernstein`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The affine Bernstein theorem in dimensions three through nine*, OpenAI Math Release, September 24, 2026, result family 353, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.AffineBernstein.affineEpigraph_sphere_inverseArea_two_flat_lintegral` of [lean/OAI/Analysis/AffineBernstein/WholeSphereInverse.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/WholeSphereInverse.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.AffineBernstein`, with `open Set MeasureTheory`, `open scoped BigOperators ContDiff ENNReal`, `open intervalIntegral`, `open scoped Pointwise`, `open Filter`, `open scoped Topology`):
--
--   ```lean
--   theorem affineEpigraph_sphere_inverseArea_two_flat_lintegral {n : ℕ} {Ω : Set (Space n)}
--       (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
--       (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
--       (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
--       {D : Set S} (hD : IsOpen D)
--       (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
--       {s : S} (hs : s ∈ D) (bS : Module.Basis ι ℝ S)
--       (bF : OrthonormalBasis κ ℝ F) (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
--       (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (v : ι → ℝ) :
--       let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
--       let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
--       let flatEnergy := fun h : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E => fun x : F =>
--         ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) bS)
--           (tubeRadiusMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) (flatProductFiberBasis bF h)) δ *
--           (‖supportConormal H (s,h (WithLp.toLp 2 (x,(1:ℝ))))‖ *
--             inverseMatrixPair (tubeBaseMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) bS) v v))
--       (∫⁻ e : Metric.sphere (0:E) 1, ENNReal.ofReal
--         ((Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
--           Real.rpow (tubeAngularDensity H (s,e) bRef) (1-δ)) *
--           (‖supportConormal H (s,e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,e) bS) v v))
--           ∂volume.toSphere) = (∫⁻ x : F, flatEnergy f x) +
--         (∫⁻ x : F, flatEnergy (f.trans (LinearIsometryEquiv.neg ℝ)) x)
--   ```
--
--   **Definitions.** The statement is written with `OAI.AffineBernstein.affineEpigraphPullback`, `OAI.AffineBernstein.flatProductFiberBasis`, `OAI.AffineBernstein.homogeneousSupport`, `OAI.AffineBernstein.inverseMatrixPair`, `OAI.AffineBernstein.supportConormal`, `OAI.AffineBernstein.tubeAngularDensity`, `OAI.AffineBernstein.tubeAreaDensity`, `OAI.AffineBernstein.tubeBaseMatrix` and `OAI.AffineBernstein.tubeRadiusMatrix` (definitions bundle `OAIQ22Ab000` of this split); `OAI.AffineBernstein.Space` and `OAI.AffineBernstein.hessian` (the published bundle `Def_AffineBernstein`).
--
--   **Used by.** The proof of `OAI.AffineBernstein.complete_affineMaximal_uniform_spherical_cap_bound` of this split imports it.
-- source:
--   OpenAI, The affine Bernstein theorem in dimensions three through nine, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 353; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-affine-Bernstein-theorem-in-dimensions-three-through-nine-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/AffineBernstein/WholeSphereInverse.lean (declaration OAI.AffineBernstein.affineEpigraph_sphere_inverseArea_two_flat_lintegral)

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
open Set MeasureTheory
open scoped BigOperators ContDiff ENNReal
namespace AffineBernstein
open intervalIntegral
open scoped Pointwise

open Filter
open scoped Topology
variable {S E F : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S] [CompleteSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [Nontrivial E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem affineEpigraph_sphere_inverseArea_two_flat_lintegral {n : ℕ} {Ω : Set (Space n)}
    (hΩ : IsOpen Ω) (hcv : Convex ℝ Ω) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ ∞ u Ω) (hp : ∀ x ∈ Ω, (hessian u x).PosDef)
    (a : Space n × ℝ) (L : (S × E) ≃L[ℝ] (Space n × ℝ))
    {D : Set S} (hD : IsOpen D)
    (hK : ∀ s ∈ D, IsCompact {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    (hzero : ∀ s ∈ D, (0:E) ∈ interior {y | (s,y) ∈ affineEpigraphPullback Ω u a L})
    {s : S} (hs : s ∈ D) (bS : Module.Basis ι ℝ S)
    (bF : OrthonormalBasis κ ℝ F) (bRef : OrthonormalBasis (κ ⊕ Unit) ℝ E)
    (f : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E) (v : ι → ℝ) :
    let H := fun q : S × E => homogeneousSupport {y | (q.1,y) ∈ affineEpigraphPullback Ω u a L} q.2
    let δ := 1/((Fintype.card ι:ℝ)+Fintype.card κ+2)
    let flatEnergy := fun h : WithLp 2 (F × ℝ) ≃ₗᵢ[ℝ] E => fun x : F =>
      ENNReal.ofReal (tubeAreaDensity (tubeBaseMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) bS)
        (tubeRadiusMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) (flatProductFiberBasis bF h)) δ *
        (‖supportConormal H (s,h (WithLp.toLp 2 (x,(1:ℝ))))‖ *
          inverseMatrixPair (tubeBaseMatrix H (s,h (WithLp.toLp 2 (x,(1:ℝ)))) bS) v v))
    (∫⁻ e : Metric.sphere (0:E) 1, ENNReal.ofReal
      ((Real.rpow (tubeBaseMatrix H (s,e) bS).det δ *
        Real.rpow (tubeAngularDensity H (s,e) bRef) (1-δ)) *
        (‖supportConormal H (s,e)‖ * inverseMatrixPair (tubeBaseMatrix H (s,e) bS) v v))
        ∂volume.toSphere) = (∫⁻ x : F, flatEnergy f x) +
      (∫⁻ x : F, flatEnergy (f.trans (LinearIsometryEquiv.neg ℝ)) x) := by
  sorry

end AffineBernstein
end

end OAI
end
