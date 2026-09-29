-- Prove2me | Theorems.Thm_IharaLemma_IdempotentSplitting_mem_maxIdeal_iff_apply_toCornerRing_eq_zero
-- name    : IharaLemma.IdempotentSplitting.mem_maxIdeal_iff_apply_toCornerRing_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/96c8df23-83ee-5841-9e9d-000a2efe7926
-- title:
--   Maximal ideal of a splitting as kernel of a residual corner point
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring with residue field $k =$ `IsLocalRing.ResidueField 𝒪`, and let $B$ be a commutative $\mathcal{O}$-algebra. Let `Sp` be an idempotent splitting of $B$, that is: a natural number $n$, elements $e_0,\dots,e_{n-1} \in B$ forming a complete orthogonal family of idempotents, and ideals $\mathfrak{m}_0,\dots,\mathfrak{m}_{n-1}$ of $B$ such that each $\mathfrak{m}_i$ is maximal, every maximal ideal of $B$ equals some $\mathfrak{m}_i$, and $e_i \in \mathfrak{m}_j$ if and only if $i \neq j$. Fix an index $i$ and write `Sp.CornerRing i` for the corner ring attached to the idempotent $e_i$, with the ring homomorphism `Sp.toCornerRing i : B →+* Sp.CornerRing i` sending $b$ to $e_i b e_i$. Let $\pi$ be an $\mathcal{O}$-algebra homomorphism from `Sp.CornerRing i` to $k$. Then for every $x \in B$, one has $x \in \mathfrak{m}_i$ if and only if $\pi(e_i x e_i) = 0$; equivalently, $\mathfrak{m}_i$ is exactly the kernel of the composite $B \to e_i B e_i \xrightarrow{\pi} k$.
--
--   This is the dictionary identifying the $i$-th maximal ideal of an idempotent splitting of $B$ with the kernel of an arbitrary residual point of the corresponding corner ring, the form in which maximal ideals of Hecke algebras are handled. It is used in the construction of Hecke-stable corners on cohomology, in [`CohCarrier.HeckeData.exists_corner_of_genMap_of_forall_isMaximal`](thm.html#CohCarrier.HeckeData.exists_corner_of_genMap_of_forall_isMaximal) and [`CohCarrier.exists_ideal_H1_top_to_dual_baseChange_heckeTorsion_jZero_of_isAbsolutelyIrreducible`](thm.html#CohCarrier.exists_ideal_H1_top_to_dual_baseChange_heckeTorsion_jZero_of_isAbsolutelyIrreducible).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_IdempotentSplitting_mem_maxIdeal_iff_apply_toCornerRing_eq_zero.lean

import Mathlib
import Definitions.Def_IharaLemma_IdempotentSplitting

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IharaLemma

theorem IharaLemma.IdempotentSplitting.mem_maxIdeal_iff_apply_toCornerRing_eq_zero
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪] {B : Type} [CommRing B] [Algebra 𝒪 B]
    (Sp : IdempotentSplitting B) (i : Fin Sp.n)
    (π : Sp.CornerRing i →ₐ[𝒪] IsLocalRing.ResidueField 𝒪) (x : B) :
    x ∈ Sp.𝔪 i ↔ π (Sp.toCornerRing i x) = 0 := by sorry
