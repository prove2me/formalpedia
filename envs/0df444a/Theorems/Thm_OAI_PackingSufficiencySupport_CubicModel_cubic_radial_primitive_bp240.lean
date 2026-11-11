-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_cubic_radial_primitive_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:48:19.497113+00:00
-- url     : https://prove2.me/theorems/fbd64840-e590-400b-86aa-9772536842ee
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive` of [lean/OAI/Geometry/BallPacking/Normal/CubicToricAmbient.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CubicToricAmbient.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped ContDiff Manifold Topology`, `open Set Function Filter Manifold`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial`):
--
--   ```lean
--    theorem cubic_radial_primitive_bp240 {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ)
--       {L : ℝ} (hL : 0<L)
--       {Ξ : BaseCurve × PlanePhase (Fin 2) → CubicConeSpace}
--       (hΞ : ContMDiff 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,CubicConeModel) ∞ Ξ)
--       (hΞfst : ∀ p,(Ξ p).1=p.1) {x : BaseCurve × PlanePhase (Fin 2)}
--       (hx : physicalParameter L (planeMoments x.2)∈lowerTrapezoid A B)
--       (he : ∀ᶠ q in 𝓝 x,(Ξ q).2=diskInverse latticeIndex
--         (coefficientSquares (cubicCoefficients (A := A) (B := B) D S q.1)) (physicalDiskCoordinates L q.2)) :
--       manifoldPullbackOneForm (fun _ => centralCubicPrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Ξ 0 x=
--         (productHorizontalLift (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2))
--             (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)+
--           (verticalLiouville : ManifoldOneForm (RealModel × PlanePhase (Fin 2)) (BaseCurve × PlanePhase (Fin 2)))) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.CubicModel.WeightedAffineIndex`, `OAI.PackingSufficiencySupport.CubicModel.WeightedHomogeneousIndex`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.FiniteMoment.TrapezoidWeight`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.PlanePhase`, `OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldPullbackOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.productHorizontalLift`, `OAI.PackingSufficiencySupport.MomentPolytope.Moments`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.DiskPair`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.Plane`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.diskInverse`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.latticeIndex` and `OAI.PackingSufficiencySupport.FiniteMoment.Radial.lowerTrapezoid` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.planeMoments` and `OAI.PackingSufficiencySupport.Hamiltonian.verticalLiouville` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.CubicModel.BaseCurve` (definitions bundle `OAIQ240Bp012` of this split); `OAI.PackingSufficiencySupport.CubicModel.CubicConeModel`, `OAI.PackingSufficiencySupport.CubicModel.CubicConeSpace`, `OAI.PackingSufficiencySupport.CubicModel.centralCubicPrimitive`, `OAI.PackingSufficiencySupport.CubicModel.cubicCoefficients`, `OAI.PackingSufficiencySupport.CubicModel.physicalParameter`, `OAI.PackingSufficiencySupport.CubicModel.physicalPrimitive` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.CubicModel.physicalDiskCoordinates` and `OAI.PackingSufficiencySupport.Hamiltonian.coefficientSquares` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.CubicModel.exists_actual_cubic_normal_transfer_into_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Normal/CubicToricAmbient.lean (declaration OAI.PackingSufficiencySupport.CubicModel.cubic_radial_primitive)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem cubic_radial_primitive_bp240 {A B : ℕ} (hA : 0<A) (hAB : A≤B) (D S : ℕ)
    {L : ℝ} (hL : 0<L)
    {Ξ : BaseCurve × PlanePhase (Fin 2) → CubicConeSpace}
    (hΞ : ContMDiff 𝓘(ℝ,RealModel × PlanePhase (Fin 2)) 𝓘(ℝ,CubicConeModel) ∞ Ξ)
    (hΞfst : ∀ p,(Ξ p).1=p.1) {x : BaseCurve × PlanePhase (Fin 2)}
    (hx : physicalParameter L (planeMoments x.2)∈lowerTrapezoid A B)
    (he : ∀ᶠ q in 𝓝 x,(Ξ q).2=diskInverse latticeIndex
      (coefficientSquares (cubicCoefficients (A := A) (B := B) D S q.1)) (physicalDiskCoordinates L q.2)) :
    manifoldPullbackOneForm (fun _ => centralCubicPrimitive (A := A) (B := B) D S (1/(L*Real.pi))) Ξ 0 x=
      (productHorizontalLift (E := RealModel) (M := BaseCurve) (V := PlanePhase (Fin 2))
          (physicalPrimitive (A := A) (B := B) D S (1/(L*Real.pi)) L ∘ planeMoments)+
        (verticalLiouville : ManifoldOneForm (RealModel × PlanePhase (Fin 2)) (BaseCurve × PlanePhase (Fin 2)))) x := by
  sorry

end PackingSufficiencySupport.CubicModel

end

end OAI
end
