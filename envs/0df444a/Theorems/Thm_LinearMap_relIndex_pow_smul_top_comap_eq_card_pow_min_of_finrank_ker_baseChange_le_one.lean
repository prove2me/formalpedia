-- Prove2me | Theorems.Thm_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
-- name    : LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/95521f78-ef61-5ff7-902f-8af953ca6ff7
-- title:
--   Index of varpi^s M in f⁻¹(varpi^s M) equals q^{min(s,m)}
-- statement:
--   Let $R$ be a discrete valuation ring which is a domain with finite residue field $k = \mathrm{ResidueField}(R)$, and let $M$ be a finitely generated free $R$-module. Let $f \colon M \to M$ be an injective $R$-linear endomorphism whose base change to $k$ has kernel of dimension at most $1$ as a $k$-vector space. Let $\varpi \in R$ be irreducible and $m$ a natural number such that $\det f$ is associated to $\varpi^m$ in $R$ (that is, the two generate the same ideal up to a unit). Then for every natural number $s$, writing $\varpi^s M$ for the submodule $(\varpi^s) \cdot \top$ of $M$ and $N_s$ for its preimage under $f$, the relative index of the additive subgroup $\varpi^s M$ in the additive subgroup $N_s = \{x \in M : f(x) \in \varpi^s M\}$ — i.e. the index of $\varpi^s M \cap N_s = \varpi^s M$ inside $N_s$ — equals $(\#k)^{\min(s,m)}$, where $\#k$ is the cardinality of the residue field.
--
--   This is the elementary index computation attached to the Smith normal form of $f$ over a discrete valuation ring: the hypothesis on the kernel of the reduction of $f$ forces all invariant factors but at most one to be units, so that one factor carries the whole of $\varpi^m$. It is the module-theoretic core of the two counting statements [`IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one`](thm.html#IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one) and [`IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank`](thm.html#IsDedekindDomain.HeightOneSpectrum.Extension.relIndex_adicCompletionIntegers_comap_sub_mulLeft_eq_absNorm_pow_min_of_ramificationIdx_eq_one_of_forall_lt_finrank), where $f$ is multiplication by an element minus a scalar on the integers of a completion, and it cites the Smith-normal-form statement [`LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le`](thm.html#LinearMap.exists_basis_apply_eq_smul_and_isUnit_and_card_le_of_finrank_ker_baseChange_le) for the pair of bases diagonalising $f$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem LinearMap.relIndex_pow_smul_top_comap_eq_card_pow_min_of_finrank_ker_baseChange_le_one
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Finite (IsLocalRing.ResidueField R)]
    (M : Type) [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]
    (f : M →ₗ[R] M) (hf : Function.Injective f)
    (hker : Module.finrank (IsLocalRing.ResidueField R)
        (LinearMap.ker (f.baseChange (IsLocalRing.ResidueField R))) ≤ 1)
    (ϖ : R) (hϖ : Irreducible ϖ) (m : ℕ) (hdet : Associated (LinearMap.det f) (ϖ ^ m)) (s : ℕ) :
    ((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).toAddSubgroup).relIndex
        (((Ideal.span {ϖ ^ s} • ⊤ : Submodule R M).comap f).toAddSubgroup) =
      Nat.card (IsLocalRing.ResidueField R) ^ min s m := by sorry
