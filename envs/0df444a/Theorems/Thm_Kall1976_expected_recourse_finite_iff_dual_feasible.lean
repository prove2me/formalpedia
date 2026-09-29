-- Prove2me | Theorems.Thm_Kall1976_expected_recourse_finite_iff_dual_feasible
-- name    : Kall1976.expected_recourse_finite_iff_dual_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-21T07:13:10.259673+00:00
-- url     : https://prove2.me/theorems/05da8834-2d1e-4444-8494-da76807478f3
-- title:
--   Theorem 15: finiteness iff almost-sure dual feasibility
-- statement:
--   Under complete fixed recourse and any one of the four stated moment alternatives, the signed expected recourse at an arbitrary first-stage decision is real-valued if and only if the dual system W transpose z at most q is feasible almost surely.
-- source:
--   Peter Kall, Stochastic Linear Programming, Springer, 1976, Chapter III section 3, Theorem 15, printed p. 54 / PDF60; complete recourse printed p. 51 / PDF57; moment assumptions in Theorem 10 and Corollary 11, printed pp. 46-48 / PDF52-54; expectation equation (8), printed p. 44 / PDF50. https://doi.org/10.1007/978-3-642-66252-2.

import Definitions.Def_Kall1976_RecourseDifferentiability
import Definitions.Def_KallMayer_Recourse_CompleteRecourse

open MeasureTheory

namespace Kall1976

/-- Kall (1976), III.15, printed54/PDF60, with the four moment alternatives
of III.10–11 (printed46–48). Complete recourse makes every right-hand side
feasible; finite expected cost is equivalent to almost-sure dual feasibility.
The data law formulation retains arbitrary joint distributions of (A,b,q).
Finiteness is existence of a real value of the signed extended expectation,
not of its totalized real projection. No finiteness premise is inherited from
III.10: III.15 cites only its integrability conditions. The source fixes any x.
All definitions are reused unchanged; no auxiliary theorem is introduced. -/
theorem expected_recourse_finite_iff_dual_feasible
    {m n p : ℕ} (μ : Measure (RecourseData m n p)) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin p) ℝ)
    (hcomplete : KallMayer.Recourse.CompleteRecourse W)
    (hmoments : recourseMomentAlternative μ)
    (x : Fin n → ℝ) :
    (∃ v : ℝ, extendedExpectedRecourse μ W x = (v : EReal)) ↔
      (∀ᵐ d ∂μ, ∃ z : Fin m → ℝ,
        ∀ j : Fin p, Matrix.mulVec W.transpose z j ≤ d.2.2 j) := by sorry

end Kall1976
