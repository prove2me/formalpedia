-- Prove2me | Theorems.Thm_HorizontalPadicL_elliptic_curve_nonvanishing
-- name    : HorizontalPadicL.elliptic_curve_nonvanishing
-- status  : Open
-- author  : @davidloeffler
-- created : 2026-09-17T06:42:05.329634+00:00
-- url     : https://prove2.me/theorems/53466256-0006-44f1-b2e6-81abf6f407e1
-- title:
--   Theorem 1.1(1) — fixed-order nonvanishing for one elliptic curve
-- statement:
--   For every complex embedding of the algebraic numbers, every modular elliptic curve over the rationals, and every d congruent to 2 modulo 4 with d at least 6, the number of primitive exact-order-d characters of conductor at most X, conductor coprime to the least modular level, and nonzero MTT twisted critical value at j = 0 has a lower bound of the stated logarithmic-power form for some positive exponent.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, p. 3, Theorem 1.1(1); pp. 41–42, Corollary 5.17.

import Definitions.Def_KN_HorizontalPadicL

set_option autoImplicit false

open scoped BigOperators NNReal

namespace HorizontalPadicL

theorem elliptic_curve_nonvanishing
    (ι : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic] (d : ℕ)
    (hmod : IsModular E) (hcase1 : d % 4 = 2 ∧ 6 ≤ d) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound (nonvanishingCount ι E hmod d) α := by sorry

end HorizontalPadicL
