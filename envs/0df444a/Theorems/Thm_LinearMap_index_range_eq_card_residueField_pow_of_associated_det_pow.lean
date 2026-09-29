-- Prove2me | Theorems.Thm_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow
-- name    : LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/d1c3db5d-d207-54de-96d8-21a52036af63
-- title:
--   Index of the image equals q^{ ord(det f)}
-- statement:
--   Let $R$ be a commutative ring that is a domain and a discrete valuation ring whose residue field $\mathrm{ResidueField}(R)$ is finite, and let $M$ be an $R$-module that is free and finitely generated over $R$. Let $f \colon M \to M$ be an $R$-linear endomorphism which is injective as a map of underlying sets, let $\varpi \in R$ be an irreducible element, and let $m$ be a natural number such that $\det f$ and $\varpi^{m}$ are associated in $R$, i.e. differ by a unit factor. The conclusion is that the index of the additive subgroup underlying the image submodule $\operatorname{range} f \subseteq M$ equals $\bigl(\#\,\mathrm{ResidueField}(R)\bigr)^{m}$, the cardinality of the residue field raised to the power $m$. Since the residue field is finite and nonzero, the right-hand side is a positive natural number; as the index is defined to be $0$ for subgroups of infinite index, the statement in particular asserts that $f(M)$ has finite index in $M$.
--
--   This is the classical formula expressing the index of the image of an injective endomorphism of a finite free module over a discrete valuation ring with finite residue field as the reciprocal of the normalised absolute value of its determinant, equivalently $[M : f(M)] = \#\bigl(R/(\det f)\bigr)$. It is obtained from the Smith-normal-form statement [`LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le`](thm.html#LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le), and is used in the local computations attached to automorphic forms, where it supplies the index of an order or lattice inside another via a determinant valuation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_index_range_eq_card_residueField_pow_of_associated_det_pow.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.index_range_eq_card_residueField_pow_of_associated_det_pow
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) :
    (LinearMap.range f).toAddSubgroup.index = Nat.card (IsLocalRing.ResidueField R) ^ m := by sorry
