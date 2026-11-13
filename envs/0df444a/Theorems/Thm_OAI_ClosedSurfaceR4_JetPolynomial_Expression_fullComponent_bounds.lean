-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_Expression_fullComponent_bounds
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.Expression.fullComponent_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:33:14.662252+00:00
-- url     : https://prove2.me/theorems/3e986090-0f1d-4358-95d3-8bf08c4c45f1
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.Expression.fullComponent_bounds: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.Expression.fullComponent_bounds` of [lean/OAI/Geometry/SurfaceImmersion/Correction/JetPolynomialFullCorrector.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/JetPolynomialFullCorrector.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, with `open scoped ContDiff`, `open PeriodicCorrector CovarianceCorrector`):
--
--   ```lean
--   theorem fullComponent_bounds (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
--       (q : LowJet → ℝ) (L : E →L[ℝ] ℝ) (v : Fin 2) (h j e : Expression)
--       (N R : ℕ) (hN : 2 ≤ N) (hh : h.order ≤ N) (hj : j.order ≤ N) (he : e.order ≤ N)
--       (lh : h.loss ≤ R) (lj : j.loss ≤ R) (le : e.loss ≤ R) :
--       (fullComponent Y C X₀ V q L v h j e).order ≤ N + 1 ∧
--         (fullComponent Y C X₀ V q L v h j e).loss ≤ R + 1
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Expression.loss` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.order` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.Expression.fullComponent` (definitions bundle `OAIQ249SI007` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_longitudinal_profile`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_mixed_profile`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_scaled_longitudinal_profile` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_transverse_profiles` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/JetPolynomialFullCorrector.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.Expression.fullComponent_bounds)

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
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial
open PeriodicCorrector CovarianceCorrector

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

namespace Expression

omit [CompleteSpace E] [FiniteDimensional ℝ E] in
theorem fullComponent_bounds (Y C X₀ : LowJet → E) (V : LowJet → C(Period, E))
    (q : LowJet → ℝ) (L : E →L[ℝ] ℝ) (v : Fin 2) (h j e : Expression)
    (N R : ℕ) (hN : 2 ≤ N) (hh : h.order ≤ N) (hj : j.order ≤ N) (he : e.order ≤ N)
    (lh : h.loss ≤ R) (lj : j.loss ≤ R) (le : e.loss ≤ R) :
    (fullComponent Y C X₀ V q L v h j e).order ≤ N + 1 ∧
      (fullComponent Y C X₀ V q L v h j e).loss ≤ R + 1 := by
  sorry

end Expression
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end
