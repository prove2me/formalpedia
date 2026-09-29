-- Prove2me | Theorems.Thm_HorizontalPadicL_realizedHorizontalCharacter_even_of_odd_prime_v2
-- name    : HorizontalPadicL.realizedHorizontalCharacter_even_of_odd_prime_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:29:37.868159+00:00
-- url     : https://prove2.me/theorems/81e913e3-4d03-46c8-bf4f-e2fed0c3cb4a
-- title:
--   Horizontal characters at an odd prime have even realizations
-- statement:
--   The order of a realized horizontal character is a power of the odd prime p. Its value at -1 has order at most two, so that value is one.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Corollary 3.6 and Corollary 5.4; standard Dirichlet-character and modular-symbol identities.

import Definitions.Def_KN_SeededInverseThetaSystemV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- A realized horizontal character is even when the horizontal prime is odd:
its order is a power of `p`, while its value at `-1` has order at most two. -/
theorem realizedHorizontalCharacter_even_of_odd_prime_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (hR : R.HasExpectedProperties) (hpodd : p ≠ 2)
    (χ : HorizontalCharacter p L.exponent) :
    (R.realized χ).2 (-1) = 1 := by
  sorry

end HorizontalPadicL
