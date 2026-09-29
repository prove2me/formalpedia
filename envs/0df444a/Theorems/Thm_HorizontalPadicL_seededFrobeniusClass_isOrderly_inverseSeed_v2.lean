-- Prove2me | Theorems.Thm_HorizontalPadicL_seededFrobeniusClass_isOrderly_inverseSeed_v2
-- name    : HorizontalPadicL.seededFrobeniusClass_isOrderly_inverseSeed_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:22:38.318562+00:00
-- url     : https://prove2.me/theorems/4a0a212c-0f78-4374-b5f2-5776b69e63a0
-- title:
--   The seeded Frobenius class consists of orderly primes (inverse-seed convention)
-- statement:
--   Assume the seed character has order at least two and its order is prime to $p$. Every prime $\ell$ in the simultaneous Frobenius class is orderly of exponent $m$. The local expression is a $p$-adic unit because modulo the maximal ideal it is
--
--   $$2\eta(\ell)-1-\eta(\ell)^2=-(\eta(\ell)-1)^2,$$
--
--   and a nontrivial root of unity of order prime to $p$ remains nontrivial after reduction.
--
--   This replacement uses the inverse-seed convention matching MTT criticalLValue: the orderly-prime expression and Euler augmentation are eta(l)*a_l - eta(l)^2 - epsilon(l). The critical values and seed hypotheses themselves retain the character eta. It supersedes `HorizontalPadicL.seededFrobeniusClass_isOrderly`.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, §4.3, Lemma 4.14 and Corollary 4.15, pp. 30–31.

import Definitions.Def_KN_SeededPrimeGaloisDataV2
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false

namespace HorizontalPadicL

theorem seededFrobeniusClass_isOrderly_inverseSeed_v2
    {N k p m B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {f : MTT.Eigenform N k ι} {η : DirichletCharacterWithLevel}
    {V : SeededEigenformPadicPlaceData (p := p) f η}
    (D : SeededOrderlyFrobeniusClassData f η m B V)
    (hηorder : 2 ≤ orderOf η.2)
    (horderCoprime : Nat.Coprime (orderOf η.2) p) :
    ∀ ⦃ℓ : ℕ⦄, ℓ ∈ D.primes →
      IsOrderlyPrimeForSeededEigenformV3 p m V.embedding f η ℓ := by sorry

end HorizontalPadicL
