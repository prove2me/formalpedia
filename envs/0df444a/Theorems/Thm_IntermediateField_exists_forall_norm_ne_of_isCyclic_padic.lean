-- Prove2me | Theorems.Thm_IntermediateField_exists_forall_norm_ne_of_isCyclic_padic
-- name    : IntermediateField.exists_forall_norm_ne_of_isCyclic_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/bfe26901-f6fc-5ee5-9430-ad419b4be249
-- title:
--   Existence of non-norms in a cyclic p-adic extension
-- statement:
--   Let $q$ be a natural number assumed prime, let $\overline{\mathbb{Q}}_q$ denote the fixed algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$, and let $K$ be an intermediate field of $\mathbb{Q}_q \subseteq \overline{\mathbb{Q}}_q$ which is finite-dimensional over $\mathbb{Q}_q$. Let $L$ be an intermediate field of $K \subseteq \overline{\mathbb{Q}}_q$ which is finite-dimensional over $K$ and Galois over $K$, and assume that the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ is cyclic. Assume moreover that the $K$-dimension of $L$ is not equal to $1$, i.e. that the extension $L/K$ is non-trivial. Then there exists a unit $a$ of the ring $K$ (that is, an element of $K^\times$) such that for every element $w$ of $L$ the norm $N_{L/K}(w)$, in Mathlib's sense `Algebra.norm K w` (the determinant of multiplication by $w$ on $L$ as a $K$-module), is different from the image of $a$ in $K$. In other words, some element of $K^\times$ is not a norm from $L$ — the quantifier ranges over all $w \in L$, including $w = 0$.
--
--   This is the classical statement that in a non-trivial finite cyclic extension of $p$-adic fields the norm map is not surjective onto the multiplicative group of the base, equivalently that $H^2(\mathrm{Gal}(L/K), L^\times)$ is non-trivial. It is used in the local analysis of Kummer cocycles, being cited by [`groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic`](thm.html#groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IntermediateField_exists_forall_norm_ne_of_isCyclic_padic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem IntermediateField.exists_forall_norm_ne_of_isCyclic_padic
    (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (L : IntermediateField K (PadicAlgCl q)) [FiniteDimensional K L] [IsGalois K L]
    (hcyc : IsCyclic (L ≃ₐ[K] L)) (hL : Module.finrank K L ≠ 1) :
    ∃ a : (↥K)ˣ, ∀ w : L, Algebra.norm K w ≠ (a : K) := by sorry
