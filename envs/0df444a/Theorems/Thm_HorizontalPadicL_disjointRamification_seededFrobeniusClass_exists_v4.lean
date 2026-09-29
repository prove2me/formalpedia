-- Prove2me | Theorems.Thm_HorizontalPadicL_disjointRamification_seededFrobeniusClass_exists_v4
-- name    : HorizontalPadicL.disjointRamification_seededFrobeniusClass_exists_v4
-- status  : Open
-- author  : @davidloeffler
-- created : 2026-09-25T14:18:08.154895+00:00
-- url     : https://prove2.me/theorems/6eddaf9a-6e8c-497f-b780-ea0879245886
-- title:
--   Simultaneous Frobenius class from faithful Galois characters
-- statement:
--   Combine the residual representation with faithful cyclotomic and seed Galois-character data. Disjoint ramification supplies a Chebotarev class with trivial residual and cyclotomic components and a full-order seed component.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Section 4.3, Lemma 4.14 and Corollary 4.15.

import Definitions.Def_KN_SeedCyclotomicGaloisCharactersV3B

set_option autoImplicit false

namespace HorizontalPadicL

/-- Disjoint ramification between the residual/cyclotomic extension and the
seed-character extension gives a simultaneous seeded Frobenius class. -/
theorem disjointRamification_seededFrobeniusClass_exists_v4
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k) (heven : Even k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (η : DirichletCharacterWithLevel)
    (m B : ℕ) (hB : 0 < B)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor)
    (V : SeededEigenformPadicPlaceData (p := p) f η)
    (R : ResidualEigenformRepresentationData f η V)
    (C : SeedCyclotomicGaloisCharacterDataV2 N p m η) :
    Nonempty (SeededOrderlyFrobeniusClassData f η m B V) := by sorry

end HorizontalPadicL
