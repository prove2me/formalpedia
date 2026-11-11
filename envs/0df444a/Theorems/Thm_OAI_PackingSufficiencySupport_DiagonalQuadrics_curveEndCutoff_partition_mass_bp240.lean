-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_curveEndCutoff_partition_mass_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:54:18.124867+00:00
-- url     : https://prove2.me/theorems/4f8cd3f1-ced0-4435-a99d-fc28e9a70545
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass` of [lean/OAI/Geometry/BallPacking/SurfaceArea/QuadricEndResidueMass.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/QuadricEndResidueMass.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Manifold Topology`, `open Set Function Filter Manifold MeasureTheory`, `open Hamiltonian`):
--
--   ```lean
--   theorem curveEndCutoff_partition_mass_bp240 {I : Type*} [Fintype I] {K : Set (locus a)}
--       (hK : IsCompact K)
--       (B : I → SurfaceCoordinateBox (locus a))
--       (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (locus a) K)
--       (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
--       {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
--       (hr : 0 < r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
--       (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
--       (hκK : tsupport (curveEndCutoff a g)⊆K)
--       (hSK : ∀ ε : Fin m → Bool,curveEndAnnulus a ε r R⊆K) (c : ℝ)
--       (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
--       (hβ : ∀ ε,ContDiff ℝ ∞ (β ε))
--       (he : ∀ ε,β ε=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c) :
--       partitionFormMass B ρ (fun x => curveEndCutoff a g x • curveFSForm a c x)=
--         (2:ℝ)^m*c*Real.pi-∑ ε : Fin m → Bool,∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityRegion`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.SurfaceCoordinateBox`, `OAI.PackingSufficiencySupport.Hamiltonian.radiusSq` and `OAI.PackingSufficiencySupport.Hamiltonian.SurfaceCoordinateBox.carrier` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.partitionFormMass` and `OAI.PackingSufficiencySupport.Hamiltonian.planarCurl` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.radialAnnulus` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndAnnulus`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveFSForm` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityRegularPrimitive` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proofs of `OAI.PackingSufficiencySupport.DiagonalQuadrics.largeHorizontalPrimitive_area_limit_bp240` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.normalHorizontalPrimitive_area_limit_bp240` of this split import it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/QuadricEndResidueMass.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff_partition_mass)

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

namespace PackingSufficiencySupport.DiagonalQuadrics
open scoped ContDiff Manifold Topology
open Set Function Filter Manifold MeasureTheory
open Hamiltonian

variable {m : ℕ} (a : Fin m → ℂ) [Fact (Injective a)] [Fact (∀ j,a j≠0)]

theorem curveEndCutoff_partition_mass_bp240 {I : Type*} [Fintype I] {K : Set (locus a)}
    (hK : IsCompact K)
    (B : I → SurfaceCoordinateBox (locus a))
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) (locus a) K)
    (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {g : ℝ → ℝ} {r R : ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (hr : 0 < r) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hκK : tsupport (curveEndCutoff a g)⊆K)
    (hSK : ∀ ε : Fin m → Bool,curveEndAnnulus a ε r R⊆K) (c : ℝ)
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (hβ : ∀ ε,ContDiff ℝ ∞ (β ε))
    (he : ∀ ε,β ε=ᶠ[𝓝ˢ (radialAnnulus 0 R)] infinityRegularPrimitive a ε c) :
    partitionFormMass B ρ (fun x => curveEndCutoff a g x • curveFSForm a c x)=
      (2:ℝ)^m*c*Real.pi-∑ ε : Fin m → Bool,∫ z : Plane,g (radiusSq z)*planarCurl (β ε) z := by
  sorry

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end
