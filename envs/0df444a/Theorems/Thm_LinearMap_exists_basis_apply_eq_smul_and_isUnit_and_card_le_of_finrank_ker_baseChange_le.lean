-- Prove2me | Theorems.Thm_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le
-- name    : LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/63be8f67-bb2d-5024-bdd5-c38dee2df99b
-- title:
--   Smith normal form with at most r non-unit factors
-- statement:
--   Let $R$ be a commutative ring that is a domain, a principal ideal ring and a local ring, with residue field $k =$ `IsLocalRing.ResidueField R`, and let $M$ be an $R$-module that is free and finitely generated. Let $f \colon M \to M$ be an $R$-linear endomorphism which is injective as a function, and let $r$ be a natural number such that the base change $f \otimes_R k \colon k \otimes_R M \to k \otimes_R M$ has kernel of dimension at most $r$ over $k$. Then there exist a natural number $n$, two bases $b, b' \colon \mathrm{Fin}\,n \to M$ of $M$ over $R$, a family of scalars $a \colon \mathrm{Fin}\,n \to R$ and a finite set $s \subseteq \mathrm{Fin}\,n$ such that $f(b_i) = a_i \cdot b'_i$ for every $i$, the scalar $a_i$ is a unit of $R$ for every $i \notin s$, and the cardinality of $s$ is at most $r$. No divisibility relations among the $a_i$ are asserted, and $n$ is produced as part of the existential rather than fixed in advance (it is in fact the rank of $M$).
--
--   This is the Smith normal form (elementary divisor form) of an injective endomorphism of a finite free module over a local principal ideal domain, sharpened by the count of non-unit elementary divisors in terms of the dimension of the kernel of the reduction modulo the maximal ideal. It is used in the computation of indices of images of such endomorphisms, by [`LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow`](thm.html#LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow) and [`LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one`](thm.html#LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le
    (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [IsLocalRing R]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f) (r : ℕ)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ r) :
    ∃ (n : ℕ) (b b' : Module.Basis (Fin n) R M) (a : Fin n → R) (s : Finset (Fin n)),
      (∀ i, f (b i) = a i • b' i) ∧ (∀ i ∉ s, IsUnit (a i)) ∧ s.card ≤ r := by sorry
