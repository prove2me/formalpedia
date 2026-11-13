-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_PhaseMean_polynomial_linear_mean_budgets
-- name    : OAI.ClosedSurfaceR4.PhaseMean.polynomial_linear_mean_budgets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T10:15:28.412385+00:00
-- url     : https://prove2.me/theorems/5b07808d-8579-48a9-b27a-fcc1d1de1a53
-- title:
--   OAI.ClosedSurfaceR4.PhaseMean.polynomial_linear_mean_budgets: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.PhaseMean.polynomial_linear_mean_budgets` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialLinearMeanBudgets.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialLinearMeanBudgets.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.PhaseMean`, with `open Set`, `open scoped ContDiff`, `open SmallModes RealModes PhaseGeometry WeightedEstimates`):
--
--   ```lean
--   theorem polynomial_linear_mean_budgets :
--       ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
--       ∀ {F : RField 4} {U : Set Base}, ContDiff ℝ ∞ F → ∀ hU : IsOpen U,
--       ∀ {ξ : Base} (hξ : ξ ≠ 0) {s : ℝ}, 0 < s → s ≤ 1 →
--       ∀ (ψ : Base → ℝ) (Q : Tensor →L[ℝ] ℝ) (B P : ℕ → ℝ),
--         (∀ m, 1 ≤ B m) → (∀ m, 1 ≤ P m) →
--         (∀ m, ‖ξ‖ ≤ B m ∧ ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧
--           ‖Q‖ ≤ B m ∧
--           (∀ j ≤ m+2, WeightedBound U 1 j (B m/s^(j-2)) F) ∧
--           (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B m) ∧
--           (∀ x ∈ U, ‖secondQuadratic (realSecondTensor F x) (-ξ.2,ξ.1)‖⁻¹ ≤ B m)) →
--         (∀ x ∈ U, Function.Injective (fderiv ℝ F x)) →
--         (∀ x ∈ U, Good (realSecondTensor F x) ξ) →
--         (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (P m) ψ) →
--         ∃ d : Budgets U (linearPhaseChart ξ hξ U hU).target s
--           (F ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
--           (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm,
--           ∀ m, d.inv m ≤ linearMeanGeometryBudget p A B P m ∧
--             d.chi m ≤ linearMeanGeometryBudget p A B P m ∧
--             d.forms m ≤ linearMeanGeometryBudget p A B P m ∧
--             d.pull m ≤ linearMeanGeometryBudget p A B P m ∧
--             d.psi m ≤ linearMeanGeometryBudget p A B P m ∧
--             d.normal m ≤ linearMeanGeometryBudget p A B P m ∧
--             d.mode m ≤ linearMeanGeometryBudget p A B P m
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.NormalFrame.Vec`, `OAI.ClosedSurfaceR4.NormalFrame.gramDet`, `OAI.ClosedSurfaceR4.PhaseMean.Tensor` and `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.PhaseMean.linearMeanGeometryBudget` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.PhaseGeometry.Good`, `OAI.ClosedSurfaceR4.PhaseGeometry.linearPhaseChart`, `OAI.ClosedSurfaceR4.PhaseGeometry.phaseEquiv`, `OAI.ClosedSurfaceR4.PhaseGeometry.secondQuadratic`, `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.RealModes.realSecondTensor`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.SmallModes.coordDeriv`, `OAI.ClosedSurfaceR4.SmallModes.dx` and `OAI.ClosedSurfaceR4.SmallModes.dy` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.PhaseMean.Budgets` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.polynomial_grid_mean_data` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialLinearMeanBudgets.lean (declaration OAI.ClosedSurfaceR4.PhaseMean.polynomial_linear_mean_budgets)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped ContDiff
namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes PhaseGeometry WeightedEstimates

theorem polynomial_linear_mean_budgets :
    ∃ (p : ℕ → ℕ) (A : ℕ → ℝ), (∀ m, 1 ≤ A m) ∧
    ∀ {F : RField 4} {U : Set Base}, ContDiff ℝ ∞ F → ∀ hU : IsOpen U,
    ∀ {ξ : Base} (hξ : ξ ≠ 0) {s : ℝ}, 0 < s → s ≤ 1 →
    ∀ (ψ : Base → ℝ) (Q : Tensor →L[ℝ] ℝ) (B P : ℕ → ℝ),
      (∀ m, 1 ≤ B m) → (∀ m, 1 ≤ P m) →
      (∀ m, ‖ξ‖ ≤ B m ∧ ‖(phaseEquiv ξ hξ).symm.toContinuousLinearMap‖ ≤ B m ∧
        ‖Q‖ ≤ B m ∧
        (∀ j ≤ m+2, WeightedBound U 1 j (B m/s^(j-2)) F) ∧
        (∀ x ∈ U, ‖(NormalFrame.gramDet (coordDeriv dx F x) (coordDeriv dy F x))⁻¹‖ ≤ B m) ∧
        (∀ x ∈ U, ‖secondQuadratic (realSecondTensor F x) (-ξ.2,ξ.1)‖⁻¹ ≤ B m)) →
      (∀ x ∈ U, Function.Injective (fderiv ℝ F x)) →
      (∀ x ∈ U, Good (realSecondTensor F x) ξ) →
      (∀ m, WeightedBound (linearPhaseChart ξ hξ U hU).target s m (P m) ψ) →
      ∃ d : Budgets U (linearPhaseChart ξ hξ U hU).target s
        (F ∘ (linearPhaseChart ξ hξ U hU).symm) ψ (fun _ => Q)
        (linearPhaseChart ξ hξ U hU) (linearPhaseChart ξ hξ U hU).symm,
        ∀ m, d.inv m ≤ linearMeanGeometryBudget p A B P m ∧
          d.chi m ≤ linearMeanGeometryBudget p A B P m ∧
          d.forms m ≤ linearMeanGeometryBudget p A B P m ∧
          d.pull m ≤ linearMeanGeometryBudget p A B P m ∧
          d.psi m ≤ linearMeanGeometryBudget p A B P m ∧
          d.normal m ≤ linearMeanGeometryBudget p A B P m ∧
          d.mode m ≤ linearMeanGeometryBudget p A B P m := by
  sorry

end ClosedSurfaceR4.PhaseMean

end

end OAI
end
