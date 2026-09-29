-- Prove2me | Theorems.Thm_HorizontalPadicL_minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
-- name    : HorizontalPadicL.minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T03:09:42.721277+00:00
-- url     : https://prove2.me/theorems/d272ba0e-3251-48b4-a5bb-dd950bb7cf25
-- title:
--   Ramified primes: $p\mid N_E \iff \deg$ local Euler factor $<2$
-- statement:
--   Let $E/\mathbb{Q}$ be a modular elliptic curve with modular conductor $N_E$, and let $p$ be a prime. Then $p$ divides the conductor exactly when the local Euler polynomial of $E$ at $p$ has degree strictly below two:
--
--   $$p\mid N_E \iff \deg L_p(E,\cdot) < 2.$$
--
--   This is the ramified direction of the characterisation of the prime support of the minimal modular level. Degree below two at $p$ is precisely the signature of bad reduction: the local factor loses a root, being linear in the multiplicative case and constant in the additive case, whereas good reduction produces the full quadratic factor.
--
--   It is stated separately from the unramified direction because the two describe complementary sets of primes and are used at different points: arguments about the level need the ramified characterisation, while arguments about Euler products away from the level need the unramified one.
-- source:
--   D. Kriz, A. Nordentoft, Horizontal p-adic L-functions; the identification of the prime support of the minimal modular level of an elliptic curve with the set of places whose local Euler polynomial has degree below two. The statement is a conjunction of the ramified and the unramified characterisation; this lemma is one of the two directions.

import Definitions.Def_HorizontalPadicL_LocalEulerFactorDegree

set_option autoImplicit false

namespace HorizontalPadicL

theorem minimalModularLevel_dvd_iff_localEulerFactorDegreeBelowTwo
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E)
    (p : ℕ) (hp : p.Prime) :
    (p ∣ modularConductor E hmod ↔ LocalEulerFactorDegreeBelowTwo E p) := by
  sorry

end HorizontalPadicL
