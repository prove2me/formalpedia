-- Prove2me | Theorems.Thm_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn
-- name    : GaloisRep.character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/44253763-64d2-587a-8851-6b4045d49523
-- title:
--   Inertia at p values of a finite-level character lie in 𝔽ₚ^×
-- statement:
--   Let $p$ be a prime and let $K$ be a field of characteristic $p$. Let $\chi$ be a monoid homomorphism from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ to the unit group $K^\times$, and assume $\chi$ factors through a finite level in the following sense: there is an intermediate field $L$ of $\mathbb{Q} \subseteq \mathrm{AlgebraicClosure}\,\mathbb{Q}$ which is finite-dimensional over $\mathbb{Q}$ and such that $\chi(\sigma) = 1$ for every automorphism $\sigma$ with $\sigma x = x$ for all $x \in L$. Let $P$ be a valuation subring of $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ lying over $p$, meaning that the image of $p$ in $\mathrm{AlgebraicClosure}\,\mathbb{Q}$ belongs to the set of nonunits of $P$. Let $\tau$ be an automorphism lying in the inertia subgroup of $P$ over $\mathbb{Q}$, viewed inside the full automorphism group as the image of the inertia subgroup under the inclusion of the decomposition subgroup of $P$ over $\mathbb{Q}$. Then $\chi(\tau)^{p-1} = 1$ in $K^\times$.
--
--   This is the standard fact that a character of the absolute Galois group of $\mathbb{Q}$ of finite level with values in a field of characteristic $p$ takes values in the prime field $\mathbb{F}_p^\times$ when restricted to inertia at $p$, i.e. that its restriction to inertia is tame of exponent dividing $p-1$. It is used in the analysis of inertial eigenvectors at $p$, feeding the statements [`GaloisRep.forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow`](thm.html#GaloisRep.forall_stableLine_false_of_inertia_eigenvector_tameCharacter_pow) and [`GaloisRep.forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd`](thm.html#GaloisRep.forall_stableLine_false_of_irreducible_of_det_inertia_pow_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn.lean

import Mathlib
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRep.character_pow_sub_one_eq_one_of_mem_inertiaSubgroupIn
    {K : Type} [Field K] (p : ℕ) [Fact p.Prime] [CharP K p]
    (χ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Kˣ)
    (hχ : GaloisFactorsThroughFiniteLevel χ)
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p)
    {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hτ : τ ∈ P.inertiaSubgroupIn ℚ) :
    χ τ ^ (p - 1) = 1 := by sorry
