-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_radialForm_positive_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.radialForm_positive_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:54:15.688972+00:00
-- url     : https://prove2.me/theorems/95cbfc84-9605-4801-ba6e-60783b47b456
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.radialForm_positive_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.radialForm_positive` of [lean/OAI/Geometry/BallPacking/SurfaceArea/CubicRadialEndSmooth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/CubicRadialEndSmooth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped ContDiff Manifold Topology BigOperators`, `open Set Function Filter Manifold`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment`):
--
--   ```lean
--   theorem radialForm_positive_bp240 {A B : ℕ} (hA : 0<A) (hAB : A≤B)
--       {D m : TrapezoidWeight A B → ℕ} (hm : ∀ i,m i<D i) {c : ℝ} (hc : 0 < c)
--       {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (b : BaseCurve) {y : RealModel}
--       (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
--       0 < chartTwoForm (radialForm Radial.latticeIndex D m c p) b y (1,0) (0,1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.FiniteMoment.TrapezoidWeight`, `OAI.PackingSufficiencySupport.Hamiltonian.chartTwoForm`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.Plane`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.latticeIndex` and `OAI.PackingSufficiencySupport.FiniteMoment.Radial.lowerTrapezoid` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.CubicModel.BaseCurve` (definitions bundle `OAIQ240Bp012` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.CubicModel.radialForm` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proofs of `OAI.PackingSufficiencySupport.CubicModel.actual_cubic_representative_packing_bp240` and `OAI.PackingSufficiencySupport.CubicModel.physicalArea_uniform_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/CubicRadialEndSmooth.lean (declaration OAI.PackingSufficiencySupport.CubicModel.radialForm_positive)

import Mathlib
import Definitions.Def_OAIQ240Bp019

section

attribute [-instance] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.surfaceSigmaCompact _root_.OAI.PackingSufficiencySupport.Hamiltonian.cylinder_chartedSpace _root_.OAI.PackingSufficiencySupport.Hamiltonian.torus_chartedSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
section

variable {ι : Type*} [Fintype ι]

theorem radialForm_positive_bp240 {A B : ℕ} (hA : 0<A) (hAB : A≤B)
    {D m : TrapezoidWeight A B → ℕ} (hm : ∀ i,m i<D i) {c : ℝ} (hc : 0 < c)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B) (b : BaseCurve) {y : RealModel}
    (hy : y∈(extChartAt 𝓘(ℝ,RealModel) b).target) :
    0 < chartTwoForm (radialForm Radial.latticeIndex D m c p) b y (1,0) (0,1) := by
  sorry

end

end PackingSufficiencySupport.CubicModel
end

end OAI
end
