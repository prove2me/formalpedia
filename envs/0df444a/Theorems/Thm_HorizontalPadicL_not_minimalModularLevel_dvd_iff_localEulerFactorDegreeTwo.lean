-- Prove2me | Theorems.Thm_HorizontalPadicL_not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo
-- name    : HorizontalPadicL.not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T03:09:45.503213+00:00
-- url     : https://prove2.me/theorems/d05bdf95-7465-4b35-9d21-2965e74b63de
-- title:
--   Unramified primes: $p
--   mid N_E \iff \deg$ local Euler factor $=2$
-- statement:
--   Let $E/\mathbb{Q}$ be a modular elliptic curve with modular conductor $N_E$, and let $p$ be a prime. Then $p$ does not divide the conductor exactly when the local Euler polynomial of $E$ at $p$ has degree two:
--
--   $$p
--   mid N_E \iff \deg L_p(E,\cdot) = 2.$$
--
--   This is the unramified direction of the characterisation of the prime support of the minimal modular level. At a prime of good reduction the local factor is the full quadratic $1-a_pX+pX^{2}$, which is what the normalisation of the Euler product away from the level requires.
--
--   It is stated separately from the ramified direction because the two describe complementary sets of primes and are used at different points of the argument.
-- source:
--   D. Kriz, A. Nordentoft, Horizontal p-adic L-functions; the identification of the prime support of the minimal modular level of an elliptic curve with the set of places whose local Euler polynomial has degree below two. The statement is a conjunction of the ramified and the unramified characterisation; this lemma is one of the two directions.

import Definitions.Def_HorizontalPadicL_LocalEulerFactorDegree

set_option autoImplicit false

namespace HorizontalPadicL

theorem not_minimalModularLevel_dvd_iff_localEulerFactorDegreeTwo
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (¬ p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeTwo E p) := by
  sorry

end HorizontalPadicL
