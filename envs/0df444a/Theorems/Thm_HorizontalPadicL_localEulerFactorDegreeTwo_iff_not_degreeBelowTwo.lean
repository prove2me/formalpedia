-- Prove2me | Theorems.Thm_HorizontalPadicL_localEulerFactorDegreeTwo_iff_not_degreeBelowTwo
-- name    : HorizontalPadicL.localEulerFactorDegreeTwo_iff_not_degreeBelowTwo
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-21T09:21:15.13715+00:00
-- url     : https://prove2.me/theorems/e45090b3-ed52-4ebf-a8e4-bb3cc22262b2
-- title:
--   Degree-two and subquadratic local Euler factors are complementary
-- statement:
--   Let $E/\mathbb Q$ be an elliptic curve and let $p$ be prime. The local Euler polynomial at $p$ has degree at most two: its degree is two at good reduction, one at multiplicative reduction, and zero at additive reduction. Consequently, it has degree exactly two if and only if it does not have degree strictly below two.
--
--   In the coefficient-side formulation used by this project, this says that the normalized quadratic recurrence
--   $$a_{p^{r+2}}=a_pa_{p^{r+1}}-p a_{p^r}$$
--   holds for every $r$ if and only if the subquadratic recurrence
--   $$a_{p^{r+2}}=a_pa_{p^{r+1}}$$
--   does not hold for every $r$.
-- source:
--   Mathlib, WeierstrassCurve.localPolynomial: the good, multiplicative, and additive cases have degrees 2, 1, and 0 respectively; https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean#L31-L41

import Definitions.Def_HorizontalPadicL_LocalEulerFactorDegree

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The local Euler polynomial of an elliptic curve has degree at most two, so
having degree two is equivalent to not having degree strictly below two. In the
coefficient-side definitions used here, this identifies the normalized
quadratic recurrence with the negation of the subquadratic recurrence. -/
theorem localEulerFactorDegreeTwo_iff_not_degreeBelowTwo
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (p : ℕ) (hp : p.Prime) :
    LocalEulerFactorDegreeTwo E p ↔
      ¬ LocalEulerFactorDegreeBelowTwo E p := by
  sorry

end HorizontalPadicL
