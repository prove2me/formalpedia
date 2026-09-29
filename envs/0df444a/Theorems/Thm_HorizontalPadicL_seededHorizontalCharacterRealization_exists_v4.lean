-- Prove2me | Theorems.Thm_HorizontalPadicL_seededHorizontalCharacterRealization_exists_v4
-- name    : HorizontalPadicL.seededHorizontalCharacterRealization_exists_v4
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:57:32.698517+00:00
-- url     : https://prove2.me/theorems/e8f578e9-29cc-4d57-9cfc-2bff02ccc5f8
-- title:
--   Faithful realization of horizontal characters exists (clean inverse-seed spine)
-- statement:
--   For every seeded horizontal prime datum, one can choose the cyclic quotient maps from the unit groups at the auxiliary primes so that every finite horizontal character is realized by an algebraic Dirichlet character. Primitive reduction preserves order, the empty-support character becomes trivial, and every primitive p-power-order character supported on the selected primes occurs.
--
--   This is the clean-spine replacement used to remove deprecated definition bundles from the live graph.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, equation (5.1), Corollary 5.4.

import Definitions.Def_KN_SeededHorizontalCharacterRealizationV2B
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The quotient maps `(Z/ℓₙZ)ˣ ↠ Z/p^(vₚ(ℓₙ-1))Z` can be chosen so that
every finite-order horizontal character is the pullback of an algebraic
Dirichlet character.  Primitive reduction preserves its order, and every
primitive `p`-power-order Dirichlet character supported on the selected primes
arises in this way.

This is the faithful replacement for
`seededHorizontalCharacterRealization_exists`: its conclusion includes the
actual pullback equation through the chosen quotient maps. -/
theorem seededHorizontalCharacterRealization_exists_v4
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    (L : SeededHorizontalPrimeDataV3 p ιp f η B) :
    ∃ R : SeededHorizontalCharacterRealizationV3 L,
      R.HasExpectedProperties := by
  sorry

end HorizontalPadicL
