-- Prove2me | Theorems.Thm_HorizontalPadicL_seedCyclotomicGaloisCharacters_exist_v4
-- name    : HorizontalPadicL.seedCyclotomicGaloisCharacters_exist_v4
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T11:46:26.935531+00:00
-- url     : https://prove2.me/theorems/5081d5cd-7574-4b9a-91ed-315ac2eb2b14
-- title:
--   Faithful cyclotomic and seed Galois characters exist
-- statement:
--   For a positive level N, a prime p, a positive exponent m, and a primitive seed Dirichlet character eta satisfying the stated order and coprimality conditions, there is a common finite Galois realization of the actual cyclotomic character modulo p^m N and the seed character, with a seed value of full character order.
-- source:
--   Standard cyclotomic-field theory: use Q(mu_{n p^m N}), reduction maps on unit residue classes, and cyclicity of finite subgroups of the multiplicative group of a field.

import Definitions.Def_KN_SeedCyclotomicGaloisCharactersV3B

set_option autoImplicit false

namespace HorizontalPadicL

/-- The actual cyclotomic character modulo `p ^ m * N` and the character cut
out by the seed Dirichlet character admit a common finite Galois realization,
and the seed image contains an element of full order. -/
theorem seedCyclotomicGaloisCharacters_exist_v4
    {N p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (η : DirichletCharacterWithLevel)
    (hηprim : η.2.IsPrimitive) (m : ℕ) (hm : 0 < m)
    (hηorder : 2 ≤ orderOf η.2)
    (horderCoprime : Nat.Coprime (orderOf η.2) p)
    (hηcoprime : Nat.Coprime (N * p) η.2.conductor) :
    Nonempty (SeedCyclotomicGaloisCharacterDataV2 N p m η) := by sorry

end HorizontalPadicL
