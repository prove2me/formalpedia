-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Perturbation_PolynomialSolveData_exists_solution
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T10:29:17.48549+00:00
-- url     : https://prove2.me/theorems/2d5aa7da-fdc0-4f81-924a-6261f1d7eec8
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialSolveData.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialSolveData.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData`, with `open TopologicalSpace`, `open scoped ContDiff NNReal`, `open WeightedEstimates PhaseMean`):
--
--   ```lean
--   theorem exists_solution (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
--       (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
--       (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q : ℕ) :
--       ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
--         (∀ m, WeightedBound Set.univ τ m (c.size f q m) X) ∧
--         (∀ m, WeightedBound Set.univ τ m (c.residual f q m)
--           (fun x => coordinateFullLinearized P ε G X x + QuadraticMean.displacement τ (coordinatePhase φ) f x))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.SupportedField`, `OAI.ClosedSurfaceR4.PhaseMean.ComplexTensor`, `OAI.ClosedSurfaceR4.QuadraticMean.RVec`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.tensorLoss` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.RealModes.RField`, `OAI.ClosedSurfaceR4.RealModes.RVec`, `OAI.ClosedSurfaceR4.SmallModes.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinatePhase` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.modeSupport` (definitions bundle `OAIQ249SI003` of this split); `OAI.ClosedSurfaceR4.QuadraticMean.displacement` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.coordinateFullLinearized`, `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.residual` and `OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.size` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.atlas_polynomial_input_cancellation_all_profiles` and `OAI.ClosedSurfaceR4.PhaseGeometry.finite_catalog_polynomial_cancellation` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialSolveData.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.Perturbation.PolynomialSolveData.exists_solution)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI007

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates PhaseMean

namespace PolynomialSolveData
variable {n : ℕ} {P : Fin 3 → Fin n → Expression} {ε τ : ℝ}
    {G : Base → Space} {hG : ContDiff ℝ ∞ G} {φ : Base → ℝ}
    {K : Compacts Base} {s : ℝ≥0}
    (c : PolynomialSolveData P ε G hG φ K τ s)

theorem exists_solution (hτ : 0 < τ) (hs : 0 < (s : ℝ)) (hτs : τ ≤ s) (hs1 : s ≤ 1)
    (hε : 0 ≤ ε) (hsmall : τ / s + ε / τ ^ tensorLoss P ≤ 1)
    (f : SupportedField (F := ComplexTensor) (modeSupport K)) (q : ℕ) :
    ∃ X : RealModes.RField 4, ContDiff ℝ ∞ X ∧ tsupport X ⊆ (modeSupport K : Set SmallModes.Base) ∧
      (∀ m, WeightedBound Set.univ τ m (c.size f q m) X) ∧
      (∀ m, WeightedBound Set.univ τ m (c.residual f q m)
        (fun x => coordinateFullLinearized P ε G X x + QuadraticMean.displacement τ (coordinatePhase φ) f x)) := by
  sorry

end PolynomialSolveData
end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
end
