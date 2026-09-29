-- Prove2me | Theorems.Thm_HorizontalPadicL_SeededHorizontalPadicLFunctionV4_primePower_propagation_v2
-- name    : HorizontalPadicL.SeededHorizontalPadicLFunctionV4.primePower_propagation_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:57:35.291606+00:00
-- url     : https://prove2.me/theorems/2cfa7bd2-46d8-4152-b8c2-1bc6e45c7c4d
-- title:
--   Quantitative propagation from a seeded horizontal measure (clean inverse-seed spine)
-- statement:
--   A seeded horizontal p-adic L-function at an odd prime, whose orderly-prime exponent is a positive integer m and whose trivial value is nonzero, yields a positive logarithmic-power lower bound for nonvanishing twists by primitive characters of exact order p^m.
--
--   This is the clean-spine replacement used to remove deprecated definition bundles from the live graph.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Section 2.3.3, Lemma 5.7, Theorem 5.9 and Corollary 5.10.

import Definitions.Def_KN_PrimePowerPropagationV2
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false

namespace HorizontalPadicL

/-- Quantitative prime-power propagation from one faithful seeded horizontal
measure. The proof sketch separates Fourier theory, realization and counting. -/
theorem SeededHorizontalPadicLFunctionV4.primePower_propagation_v2
    {N k B p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η)
    (hpodd : p ≠ 2) (m : ℕ) (hm : 0 < m)
    (hexponent : ν.primes.orderExponent = m)
    (hinterp : ν.InterpolatesSeededCriticalValuesV4)
    (htriv : ν.measure.eval
      (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0) :
    ∃ α : ℝ, 0 < α ∧
      HasLogPowerLowerBound
        (seededPrimePowerNonvanishingCount ι f η p m B) α := by
  sorry

end HorizontalPadicL
