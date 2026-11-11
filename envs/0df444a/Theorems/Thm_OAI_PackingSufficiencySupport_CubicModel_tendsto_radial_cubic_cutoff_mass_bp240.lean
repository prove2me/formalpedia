-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_CubicModel_tendsto_radial_cubic_cutoff_mass_bp240
-- name    : OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:49:39.73752+00:00
-- url     : https://prove2.me/theorems/48cd3cf6-7145-44bb-b285-0ae57e337423
-- title:
--   OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass` of [lean/OAI/Geometry/BallPacking/SurfaceArea/CubicRadialEndSmooth.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/CubicRadialEndSmooth.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.CubicModel`, with `open scoped ContDiff Manifold Topology BigOperators`, `open Set Function Filter Manifold`, `open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment`, `open MeasureTheory`):
--
--   ```lean
--   theorem tendsto_radial_cubic_cutoff_mass_bp240 {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
--       (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
--       {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B)
--       {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
--       (hr : 0 < r) (hRp : 0<R) (hR1 : R<1)
--       (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion)
--       (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ) :
--       Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
--         (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)) atTop
--         (𝓝 (c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.CubicModel.cubicDegree`, `OAI.PackingSufficiencySupport.CubicModel.cubicMarkedOrder`, `OAI.PackingSufficiencySupport.CubicModel.endRegularRegion`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.FiniteMoment.TrapezoidWeight`, `OAI.PackingSufficiencySupport.FiniteMoment.markedHeight`, `OAI.PackingSufficiencySupport.FiniteMoment.planeVector`, `OAI.PackingSufficiencySupport.Hamiltonian.shrinkingCutoff`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_injective`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.Explicit.parameters_nonzero`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.Plane`, `OAI.PackingSufficiencySupport.FiniteMoment.Radial.latticeIndex` and `OAI.PackingSufficiencySupport.FiniteMoment.Radial.lowerTrapezoid` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.surfaceCutoffMass` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.CubicModel.cubicRadialEndSmoothSigmaCompact` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.CubicModel.radialForm`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceManifold` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.shrinking_curveEndCutoff_compact` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.CubicModel.physicalArea_uniform_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/CubicRadialEndSmooth.lean (declaration OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass)

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
open scoped ContDiff Manifold Topology BigOperators
open Set Function Filter Manifold
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment
open MeasureTheory

 attribute [local instance] OAI.PackingSufficiencySupport.CubicModel.cubicRadialEndSmoothSigmaCompact
theorem tendsto_radial_cubic_cutoff_mass_bp240 {A B D S : ℕ} (hA : 0<A) (hS0 : 0<S)
    (hAB : A≤B) (hSB : S≤B) (hB : 3*B<D) (hS : 3*S<D)
    {p : Radial.Plane} (hp : p∈Radial.lowerTrapezoid A B)
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hr : 0 < r) (hRp : 0<R) (hR1 : R<1)
    (hR : {s : ℂ | Complex.normSq s≤R}⊆endRegularRegion)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R) (c : ℝ) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact (parameters 0) hr h1 n)
      (radialForm (Radial.latticeIndex (A := A) (B := B)) (cubicDegree D) (cubicMarkedOrder S) c p)) atTop
      (𝓝 (c*(3*((D:ℝ)-3*(p.1+p.2))-2*markedHeight S (planeVector p.1 p.2))*Real.pi)) := by
  sorry

end PackingSufficiencySupport.CubicModel

end

end OAI
end
