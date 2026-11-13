-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_slow_step
-- name    : OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:08:47.30272+00:00
-- url     : https://prove2.me/theorems/4bfb7a6d-6e54-46e6-9b91-f069bc77d76b
-- title:
--   OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step` of [lean/OAI/Geometry/SurfaceImmersion/Correction/MetricPolynomialSlowStep.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/MetricPolynomialSlowStep.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData`, with `open Set Manifold Bundle`, `open scoped ContDiff Manifold Topology`, `open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PrimitiveRealization`):
--
--   ```lean
--   theorem polynomial_slow_step (data : MetricGoodPhaseData g F)
--       {n : data.A.centers → ℕ}
--       (Pol : ∀ i : data.A.centers, Fin 3 → Fin (n i) → Expression)
--       (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
--       (hF : ContMDiff planeModel spaceModel ∞ F) :
--       ∃ loss : ℕ, ∀ (b b' d d' a u : ℝ), 0 ≤ b → b < b' → b'*(loss : ℝ) < 1 →
--         2*b' < d → d < d' → 2*d' < 3*d-b' → 0 < a → 0 < u →
--       ∀ (P D : ℕ → ℝ) (L : ℝ), (∀ m, 0 ≤ P m) → (∀ m, 0 ≤ D m) → 0 ≤ L →
--         (∀ m, data.A.ShiftedBound 2 m 1 (P m) F) →
--       ∃ (a' η L' : ℝ) (P' D' : ℕ → ℝ), 0 < a' ∧ 0 < η ∧ η ≤ 1 ∧ 0 ≤ L' ∧
--         (∀ m, 0 ≤ P' m) ∧ (∀ m, 0 ≤ D' m) ∧
--       ∀ z : ℝ, 0 < z → z < η → ∀ G : M → Space,
--         ContMDiff planeModel spaceModel ∞ G →
--         data.A.WeightedBound 1 3 (L*z^u) (G-F) →
--         (∀ m, data.A.ShiftedBound 2 m (z^b) (P m) G) →
--         (∀ m, data.A.TensorWeightedBound (z^b) m (D m*z^a)
--           (data.A.normalizedPolynomialDefect Pol z (z^d) g.inner G)) →
--         ∃ G' : M → Space, ContMDiff planeModel spaceModel ∞ G' ∧
--           data.A.WeightedBound 1 3 (L'*z^(min u (d-2*b'))) (G'-F) ∧
--           (∀ m, data.A.ShiftedBound 2 m (z^b') (P' m) G') ∧
--           (∀ m, data.A.TensorWeightedBound (z^b') m (D' m*z^a')
--             (data.A.normalizedPolynomialDefect Pol z (z^d') g.inner G'))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.SmoothCoeffs` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.ShiftedBound` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.WeightedBound` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.normalizedPolynomialDefect` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.TensorWeightedBound` (definitions bundle `OAIQ249SI013` of this split); `OAI.ClosedSurfaceR4.Plane`, `OAI.ClosedSurfaceR4.SmoothMetric`, `OAI.ClosedSurfaceR4.Space`, `OAI.ClosedSurfaceR4.planeModel` and `OAI.ClosedSurfaceR4.spaceModel` (the published bundle `Def_SurfaceImmersion`).
--
--   **Used by.** The proofs of `OAI_ClosedSurfaceR4_FiniteOrderSmoothing_MetricGoodPhaseData_polynomial_finite_slow_family` and `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_mean_approximation` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/MetricPolynomialSlowStep.lean (declaration OAI.ClosedSurfaceR4.FiniteOrderSmoothing.MetricGoodPhaseData.polynomial_slow_step)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv.WithinZpow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.ArithmeticGeometric
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Thickening
import Definitions.Def_SurfaceImmersion
import Definitions.Def_OAIQ249SI010

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation WeightedEstimates PrimitiveRealization
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace MetricGoodPhaseData
attribute [local instance] OAI.ClosedSurfaceR4.FiniteOrderSmoothing.slowPolynomialFiberNormed
local instance slowPolynomialFiberSpace_rf950f3_1 : NormedSpace ℝ TensorFiber := inferInstance
local instance slowPolynomialDualAdd_rf950f3_1 : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance slowPolynomialDualSmul_rf950f3_1 : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
variable {g : SmoothMetric M} {F : M → Space}

local instance slowPolynomialSectionNormed_rf950f3_1 (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance slowPolynomialSectionSpace_rf950f3_1 (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)
theorem polynomial_slow_step (data : MetricGoodPhaseData g F)
    {n : data.A.centers → ℕ}
    (Pol : ∀ i : data.A.centers, Fin 3 → Fin (n i) → Expression)
    (hPol : ∀ i k l, (Pol i k l).SmoothCoeffs univ)
    (hF : ContMDiff planeModel spaceModel ∞ F) :
    ∃ loss : ℕ, ∀ (b b' d d' a u : ℝ), 0 ≤ b → b < b' → b'*(loss : ℝ) < 1 →
      2*b' < d → d < d' → 2*d' < 3*d-b' → 0 < a → 0 < u →
    ∀ (P D : ℕ → ℝ) (L : ℝ), (∀ m, 0 ≤ P m) → (∀ m, 0 ≤ D m) → 0 ≤ L →
      (∀ m, data.A.ShiftedBound 2 m 1 (P m) F) →
    ∃ (a' η L' : ℝ) (P' D' : ℕ → ℝ), 0 < a' ∧ 0 < η ∧ η ≤ 1 ∧ 0 ≤ L' ∧
      (∀ m, 0 ≤ P' m) ∧ (∀ m, 0 ≤ D' m) ∧
    ∀ z : ℝ, 0 < z → z < η → ∀ G : M → Space,
      ContMDiff planeModel spaceModel ∞ G →
      data.A.WeightedBound 1 3 (L*z^u) (G-F) →
      (∀ m, data.A.ShiftedBound 2 m (z^b) (P m) G) →
      (∀ m, data.A.TensorWeightedBound (z^b) m (D m*z^a)
        (data.A.normalizedPolynomialDefect Pol z (z^d) g.inner G)) →
      ∃ G' : M → Space, ContMDiff planeModel spaceModel ∞ G' ∧
        data.A.WeightedBound 1 3 (L'*z^(min u (d-2*b'))) (G'-F) ∧
        (∀ m, data.A.ShiftedBound 2 m (z^b') (P' m) G') ∧
        (∀ m, data.A.TensorWeightedBound (z^b') m (D' m*z^a')
          (data.A.normalizedPolynomialDefect Pol z (z^d') g.inner G')) := by
  sorry

end MetricGoodPhaseData
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
end
