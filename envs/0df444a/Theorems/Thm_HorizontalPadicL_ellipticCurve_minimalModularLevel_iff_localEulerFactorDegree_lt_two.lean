-- Prove2me | Theorems.Thm_HorizontalPadicL_ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two
-- name    : HorizontalPadicL.ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-18T08:56:47.586505+00:00
-- url     : https://prove2.me/theorems/c7f83142-37ef-43e3-9262-ef2e86ce5f10
-- title:
--   The minimal modular level detects subquadratic local Euler factors
-- statement:
--   **This is a formalization of a standard textbook result, so low-priority**
--
--   Let $E/\mathbb{Q}$ be an elliptic curve which is modular in the sense that its Hasse–Weil $L$-series is the q-expansion of a weight-two cusp form, and let $N_{\min}$ be the least level at which such a form exists. For every prime $p$,
--   $$
--   p \mid N_{\min} \quad\Longleftrightarrow\quad L_p(E,s)^{-1} \text{ has degree }<2.
--   $$
--   In coefficient terms, primes dividing $N_{\min}$ satisfy $a_{p^{r+2}}=a_p a_{p^{r+1}}$, while primes not dividing $N_{\min}$ satisfy the normalized quadratic recurrence $a_{p^{r+2}}=a_p a_{p^{r+1}}-p a_{p^r}$. Thus the prime support of the minimal modular level agrees with the bad local-factor support of the elliptic curve.
-- source:
--   Diamond–Shurman, A First Course in Modular Forms, Proposition 5.8.5 and the newform/conductor theory in Chapter 5; Silverman, The Arithmetic of Elliptic Curves, Chapter V, §2.

import Definitions.Def_HorizontalPadicL_LocalEulerFactorDegree

set_option autoImplicit false

namespace HorizontalPadicL

/-- The prime support of the least modular level is exactly the set of places
where the elliptic curve's local Euler polynomial has degree below two;
equivalently, the primes outside the level are exactly those with the normalized
quadratic local factor. -/
theorem ellipticCurve_minimalModularLevel_iff_localEulerFactorDegree_lt_two
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeBelowTwo E p) ∧
      (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) := by
  sorry

end HorizontalPadicL
