-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_radialEndResidue_error_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:44:44.050194+00:00
-- url     : https://prove2.me/theorems/fd8df232-4cb8-4887-a1ef-24733df96641
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error` of [lean/OAI/Geometry/BallPacking/Toric/CubicRadialProbability.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Toric/CubicRadialProbability.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped BigOperators ContDiff Manifold Topology`, `open Set Function Filter Manifold`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment`):
--
--   ```lean
--    theorem radialEndResidue_error_bp240 {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
--       (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
--       {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
--       (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
--       (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion)
--       (ht : 0 < radiusSq y) (ht1 : radiusSq y<1) {M : ℝ} (hM : 0≤M)
--       (hlog : ∀ k : TrapezoidWeight A B,|Real.log (regularCoefficientNorm (cubicDegree D k) (cubicMarkedOrder S k) ε y)|≤M)
--       (c : ℝ) :
--       |radialEndResidue (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p ε y-
--         c*limitingEndOrder D S (planeVector p.1 p.2) ε|≤
--         |c| * ((2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.CubicModel.EndIndex`, `OAI.PackingSufficiencySupport.CubicModel.cubicDegree`, `OAI.PackingSufficiencySupport.CubicModel.cubicMarkedOrder`, `OAI.PackingSufficiencySupport.CubicModel.endRegularRegion`, `OAI.PackingSufficiencySupport.CubicModel.limitingEndOrder`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.FiniteMoment.TrapezoidWeight`, `OAI.PackingSufficiencySupport.FiniteMoment.planeVector`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.radiusSq`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.Plane`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.latticeIndex` and `OAI.PackingSufficiencySupport.FiniteMoment.Radial.lowerTrapezoid` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.CubicModel.radialEndResidue` and `OAI.PackingSufficiencySupport.CubicModel.regularCoefficientNorm` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/Toric/CubicRadialProbability.lean (declaration OAI.PackingSufficiencySupport.CubicModel.radialEndResidue_error)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.Comparison.convexMaps_nonempty _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped BigOperators ContDiff Manifold Topology
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment

 theorem radialEndResidue_error_bp240 {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (ε : EndIndex) {y : Plane}
    (hy : y∈(infinityDiffeomorph (parameters 0) ε).source)
    (hR : Complex.equivRealProdCLM.symm y∈endRegularRegion)
    (ht : 0 < radiusSq y) (ht1 : radiusSq y<1) {M : ℝ} (hM : 0≤M)
    (hlog : ∀ k : TrapezoidWeight A B,|Real.log (regularCoefficientNorm (cubicDegree D k) (cubicMarkedOrder S k) ε y)|≤M)
    (c : ℝ) :
    |radialEndResidue (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p ε y-
      c*limitingEndOrder D S (planeVector p.1 p.2) ε|≤
      |c| * ((2*M+Fintype.card (TrapezoidWeight A B))/(-Real.log (radiusSq y))) := by
  sorry

end PackingSufficiencySupport.CubicModel
end

end OAI
end
