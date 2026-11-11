-- Prove2me | Theorems.Thm_OAI_PackingSufficiencySupport_DiagonalQuadrics_tendsto_curveCutoff_bounded_residue_bp240
-- name    : OAI.PackingSufficiencySupport.DiagonalQuadrics.tendsto_curveCutoff_bounded_residue_bp240
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:54:03.770428+00:00
-- url     : https://prove2.me/theorems/7889ef89-24ac-42f9-bd7d-5a7ba6b58a9a
-- title:
--   OAI.PackingSufficiencySupport.DiagonalQuadrics.tendsto_curveCutoff_bounded_residue_bp240: intermediate lemma from OpenAI, Symplectic Ball Packings in Higher Dimensions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.HigherDimensionalBallPacking.main_theorem`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Symplectic Ball Packings in Higher Dimensions*, OpenAI Math Release, September 23, 2026, result family 343, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PackingSufficiencySupport.DiagonalQuadrics.tendsto_curveCutoff_bounded_residue` of [lean/OAI/Geometry/BallPacking/SurfaceArea/BoundedPlanarResidue.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/BoundedPlanarResidue.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PackingSufficiencySupport.DiagonalQuadrics`, with `open scoped ContDiff Manifold Topology`, `open Set Function Filter Manifold MeasureTheory`, `open Hamiltonian`):
--
--   ```lean
--   theorem tendsto_curveCutoff_bounded_residue_bp240
--       (α : ManifoldOneForm RealModel (locus a))
--       (hα : SmoothOneFormFamily (fun _ : ℝ => α))
--       (Ω : ManifoldTwoForm RealModel (locus a)) (hΩ : SmoothTwoForm Ω)
--       (hsk : ∀ x v w,Ω x v w= -Ω x w v) (hαΩ : manifoldExteriorOneForm α=Ω)
--       {g : ℝ → ℝ} {r R K M : ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
--       (hr : 0 < r) (hRp : 0≤R) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
--       (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
--       (hK : 0≤K) (hM : 0≤M) (hdg : ∀ t : ℝ,|deriv g t|≤K)
--       (c : (Fin m → Bool) → ℝ) (e : ℕ → ℝ) (he : ∀ n,0≤e n) (het : Tendsto e atTop (𝓝 0))
--       (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
--       (d : (Fin m → Bool) → Plane → ℝ)
--       (hβc : ∀ ε (n : ℕ),ContinuousOn (β ε) (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
--       (hdc : ∀ ε (n : ℕ),ContinuousOn (d ε) (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
--       (hβ : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → ‖β ε z‖≤M)
--       (hd : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → |d ε z-c ε|≤e n)
--       (hdecomp : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) →
--         euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,z)=
--           β ε z-(d ε z/2) • angularOneForm z) :
--       Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n) Ω)
--         atTop (𝓝 ((∑ ε : Fin m → Bool,c ε)*Real.pi))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PackingSufficiencySupport.DiagonalQuadrics.Affine`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.RealModel`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityRegion`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.locus`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.ManifoldTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.Plane`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothOneFormFamily`, `OAI.PackingSufficiencySupport.Hamiltonian.SmoothTwoForm`, `OAI.PackingSufficiencySupport.Hamiltonian.euclideanPullbackOneForm`, `OAI.PackingSufficiencySupport.Hamiltonian.manifoldExteriorOneForm` and `OAI.PackingSufficiencySupport.Hamiltonian.shrinkingCutoff` (definitions bundle `OAIQ240Bp003` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.angularOneForm` (definitions bundle `OAIQ240Bp007` of this split); `OAI.PackingSufficiencySupport.Hamiltonian.radialAnnulus` and `OAI.PackingSufficiencySupport.Hamiltonian.surfaceCutoffMass` (definitions bundle `OAIQ240Bp010` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.infinityDiffeomorph` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceChartedSpace` (definitions bundle `OAIQ240Bp015` of this split); `OAI.PackingSufficiencySupport.DiagonalQuadrics.boundedResidueLimitSigmaCompact`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.curveEndCutoff`, `OAI.PackingSufficiencySupport.DiagonalQuadrics.realSurfaceManifold` and `OAI.PackingSufficiencySupport.DiagonalQuadrics.shrinking_curveEndCutoff_compact` (definitions bundle `OAIQ240Bp019` of this split).
--
--   **Used by.** The proof of `OAI.PackingSufficiencySupport.CubicModel.tendsto_radial_cubic_cutoff_mass_bp240` of this split imports it.
-- source:
--   OpenAI, Symplectic Ball Packings in Higher Dimensions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 343; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Ball-Packings-in-Higher-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/BallPacking/SurfaceArea/BoundedPlanarResidue.lean (declaration OAI.PackingSufficiencySupport.DiagonalQuadrics.tendsto_curveCutoff_bounded_residue)

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

 attribute [local instance] OAI.PackingSufficiencySupport.DiagonalQuadrics.boundedResidueLimitSigmaCompact
theorem tendsto_curveCutoff_bounded_residue_bp240
    (α : ManifoldOneForm RealModel (locus a))
    (hα : SmoothOneFormFamily (fun _ : ℝ => α))
    (Ω : ManifoldTwoForm RealModel (locus a)) (hΩ : SmoothTwoForm Ω)
    (hsk : ∀ x v w,Ω x v w= -Ω x w v) (hαΩ : manifoldExteriorOneForm α=Ω)
    {g : ℝ → ℝ} {r R K M : ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hr : 0 < r) (hRp : 0≤R) (hR : {s : ℂ | Complex.normSq s≤R}⊆infinityRegion a)
    (h1 : ∀ t∈Ioo (-r) r,g t=1) (h0 : tsupport g⊆Iic R)
    (hK : 0≤K) (hM : 0≤M) (hdg : ∀ t : ℝ,|deriv g t|≤K)
    (c : (Fin m → Bool) → ℝ) (e : ℕ → ℝ) (he : ∀ n,0≤e n) (het : Tendsto e atTop (𝓝 0))
    (β : (Fin m → Bool) → Plane → Plane →L[ℝ] ℝ)
    (d : (Fin m → Bool) → Plane → ℝ)
    (hβc : ∀ ε (n : ℕ),ContinuousOn (β ε) (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hdc : ∀ ε (n : ℕ),ContinuousOn (d ε) (radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1))))
    (hβ : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → ‖β ε z‖≤M)
    (hd : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) → |d ε z-c ε|≤e n)
    (hdecomp : ∀ ε (n : ℕ) z,z∈radialAnnulus (r/((n:ℝ)+1)) (R/((n:ℝ)+1)) →
      euclideanPullbackOneForm (fun _ => α) (infinityDiffeomorph a ε) (0,z)=
        β ε z-(d ε z/2) • angularOneForm z) :
    Tendsto (fun n => surfaceCutoffMass (shrinking_curveEndCutoff_compact a hr h1 n) Ω)
      atTop (𝓝 ((∑ ε : Fin m → Bool,c ε)*Real.pi)) := by
  sorry

end PackingSufficiencySupport.DiagonalQuadrics

end

end OAI
end
