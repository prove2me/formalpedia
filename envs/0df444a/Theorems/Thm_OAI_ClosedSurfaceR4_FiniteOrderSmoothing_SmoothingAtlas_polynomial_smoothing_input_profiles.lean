-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_SmoothingAtlas_polynomial_smoothing_input_profiles
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:43:51.143905+00:00
-- url     : https://prove2.me/theorems/ff6973e9-8a48-4e62-953c-67b84e4d101f
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialSmoothingProfiles.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialSmoothingProfiles.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas`, with `open Set Manifold Bundle MeasureTheory`, `open scoped ContDiff Manifold Topology`, `open WeightedEstimates RealModes`):
--
--   ```lean
--   theorem polynomial_smoothing_input_profiles (r : ℕ) (B : ℝ → ℝ) (hB : HasPolynomialBound B) :
--       ∃ P C : ℕ → ℝ → ℝ,
--         (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (C m)) ∧
--         (∀ m x, 1 ≤ x → 1 ≤ C m x) ∧
--       ∀ x : ℝ, 1 ≤ x →
--         ∀ (G : M → Space) (H : ∀ y : M, CovariantTwoTensor y) (t s : ℝ),
--         0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
--         ContMDiff planeModel spaceModel ∞ G →
--         ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
--           (fun y => TotalSpace.mk' TensorFiber y (H y)) →
--         A.InputBound t r (B x) G H →
--         (∀ m, A.ShiftedBound 2 m s (P m x) (A.smooth r s G)) ∧
--         (∀ m, A.TensorWeightedBound s m (C m x) (A.tensorSmooth r s H))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.CovariantTwoTensor`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.TensorFiber` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileDualSmul` and `OAI.ClosedSurfaceR4.RealModes.HasPolynomialBound` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.smooth` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileFiberNormed` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileFiberSpace` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.tensorSmooth` (definitions bundle `OAIQ249SI012` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.InputBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.anchored_smoothed_increment` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialSmoothingProfiles.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_smoothing_input_profiles)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle MeasureTheory
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileFiberSpace
local instance polySmoothingProfileDualAdd_ra5dbb0_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileDualSmul
variable (A : SmoothingAtlas M)

attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.polySmoothingProfileFiberNormed
local instance polySmoothingProfileSectionNormed_ra5dbb0_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polySmoothingProfileSectionSpace_ra5dbb0_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_smoothing_input_profiles (r : ℕ) (B : ℝ → ℝ) (hB : HasPolynomialBound B) :
    ∃ P C : ℕ → ℝ → ℝ,
      (∀ m, HasPolynomialBound (P m)) ∧ (∀ m, HasPolynomialBound (C m)) ∧
      (∀ m x, 1 ≤ x → 1 ≤ C m x) ∧
    ∀ x : ℝ, 1 ≤ x →
      ∀ (G : M → Space) (H : ∀ y : M, CovariantTwoTensor y) (t s : ℝ),
      0 < t → t ≤ 1 → 0 < s → s ≤ 1 →
      ContMDiff planeModel spaceModel ∞ G →
      ContMDiff planeModel (planeModel.prod 𝓘(ℝ,TensorFiber)) ∞
        (fun y => TotalSpace.mk' TensorFiber y (H y)) →
      A.InputBound t r (B x) G H →
      (∀ m, A.ShiftedBound 2 m s (P m x) (A.smooth r s G)) ∧
      (∀ m, A.TensorWeightedBound s m (C m x) (A.tensorSmooth r s H)) := by
  sorry

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
