-- Prove2me | Theorems.Thm_HorizontalPadicL_SeededHorizontalCharacterRealizationV3_realizes_supported_pPower_character_v2
-- name    : HorizontalPadicL.SeededHorizontalCharacterRealizationV3.realizes_supported_pPower_character_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:50:40.558235+00:00
-- url     : https://prove2.me/theorems/c8e3b378-13d3-4aa4-b143-ef850db23f5f
-- title:
--   Supported p-power characters are realized horizontally (inverse-seed convention)
-- statement:
--   Let R be a faithful realization of horizontal characters using the maximal p-power quotients of the unit groups at the selected auxiliary primes. Every primitive Dirichlet character of p-power order whose conductor divides a finite product of selected primes is the primitive character realized by some finite horizontal character.
--
--   This replacement uses the inverse-seed convention matching MTT criticalLValue: the orderly-prime expression and Euler augmentation are eta(l)*a_l - eta(l)^2 - epsilon(l). The critical values and seed hypotheses themselves retain the character eta. It supersedes `HorizontalPadicL.SeededHorizontalCharacterRealizationV2.realizes_supported_pPower_character`.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, equation (5.1), Corollary 5.4.

import Definitions.Def_KN_SeededHorizontalCharacterRealizationV2B
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Every primitive `p`-power-order Dirichlet character supported on finitely
many selected horizontal primes is obtained from the corresponding horizontal
finite quotient. -/
theorem SeededHorizontalCharacterRealizationV3.realizes_supported_pPower_character_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (ψ : DirichletCharacterWithLevel)
    (hprimitive : ψ.2.IsPrimitive)
    (horder : ∃ a : ℕ, orderOf ψ.2 = p ^ a)
    (hsupport : ∃ A : Finset ℕ,
      ψ.2.conductor ∣ L.supportModulus A) :
    ∃ χ : HorizontalCharacter p L.exponent,
      R.realized χ = ψ := by
  sorry

end HorizontalPadicL
