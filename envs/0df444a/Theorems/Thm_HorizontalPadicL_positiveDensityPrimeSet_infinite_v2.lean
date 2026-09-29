-- Prove2me | Theorems.Thm_HorizontalPadicL_positiveDensityPrimeSet_infinite_v2
-- name    : HorizontalPadicL.positiveDensityPrimeSet_infinite_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T10:56:24.802947+00:00
-- url     : https://prove2.me/theorems/367dddd9-3bd0-4cca-a0f5-2129574ac2a1
-- title:
--   Positive-density sets of primes are infinite
-- statement:
--   A set of natural numbers with positive natural density relative to the rational primes is infinite.
-- source:
--   Standard consequence of the definition of positive prime-relative natural density.

import Definitions.Def_KN_HorizontalPadicLAux

set_option autoImplicit false

namespace HorizontalPadicL

/-- A set of natural numbers having positive natural density relative to the
rational primes is infinite. -/
theorem positiveDensityPrimeSet_infinite_v2
    (A : Set ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hdensity : HasPrimeNaturalDensity A δ) : A.Infinite := by sorry

end HorizontalPadicL
