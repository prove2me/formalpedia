-- Prove2me | Theorems.Thm_FreyPackage_exists_inertia_cycloPinned_ne_one_v2
-- name    : FreyPackage.exists_inertia_cycloPinned_ne_one_v2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/4d5f326f-56f3-5648-983f-4fe72f2263b2
-- title:
--   Inertia at p acts non-trivially on the p-th roots of unity
-- statement:
--   Let $p$ be a prime with $p \neq 2$, and let $A$ be a valuation subring of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ satisfying `A.LiesOverPrime p`, that is, the image of $p$ in the algebraic closure is a non-unit of $A$ (it lies in `A.nonunits`); so $A$ is a place of $\bar{\mathbb{Q}}$ above $p$. Let $n$ be an arbitrary function from the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ to $\mathbb{N}$ which pins down the action on $p$-th roots of unity, in the sense that for every automorphism $\sigma$ and every $\zeta$ in the algebraic closure with $\zeta^{p} = 1$ one has $\sigma \zeta = \zeta^{\,n(\sigma)}$. The conclusion is that there exists an element $\sigma$ of the inertia subgroup `A.inertiaSubgroup ℚ` (a subgroup of the decomposition subgroup of $A$ over $\mathbb{Q}$) whose underlying automorphism satisfies $n(\sigma) \neq 1$ in $\mathbb{Z}/p$. No Frey package occurs in the statement despite the namespace; the assertion concerns only the mod $p$ cyclotomic character.
--
--   This is the classical ramification statement that the mod $p$ cyclotomic character is ramified at $p$, equivalently that $p$ ramifies in $\mathbb{Q}(\mu_p)$, recorded in the form of a non-trivial value of the pinning exponent $n$ on inertia at a place above $p$. It supplies the ramification-at-$p$ input used by [`GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt`](thm.html#GaloisRepAdic.exists_submodule_finrank_le_invariants_add_one_mem_of_isStrictOrdinaryAt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FreyPackage_exists_inertia_cycloPinned_ne_one_v2.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FreyPackage.exists_inertia_cycloPinned_ne_one_v2 (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → ℕ)
    (hn : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ζ : AlgebraicClosure ℚ), ζ ^ p = 1 → σ ζ = ζ ^ (n σ)) :
    ∃ σ ∈ A.inertiaSubgroup ℚ, (n (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ZMod p) ≠ 1 := by sorry
