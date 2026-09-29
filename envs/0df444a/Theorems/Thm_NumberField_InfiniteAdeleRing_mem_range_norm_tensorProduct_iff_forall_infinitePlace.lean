-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace
-- name    : NumberField.InfiniteAdeleRing.mem_range_norm_tensorProduct_iff_forall_infinitePlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/05b850c2-982a-531b-b50e-14936d32b7bd
-- title:
--   Archimedean norms split over the infinite places
-- statement:
--   Let $K$ and $L$ be number fields, $L$ equipped with a $K$-algebra structure, and let $a$ be a unit of the infinite adele ring $\mathbb{A}_{K,\infty} = \prod_{w\mid\infty} K_w$ of $K$ (the product of the completions $K_w$ over the infinite places $w$ of $K$). Consider the base change $L \otimes_K \mathbb{A}_{K,\infty}$, regarded as an algebra over $\mathbb{A}_{K,\infty}$ through the right tensor factor, and likewise $L \otimes_K K_w$ as an algebra over $K_w$ for each infinite place $w$. The assertion is that the element of $\mathbb{A}_{K,\infty}$ underlying $a$ lies in the image of the map sending a unit $t$ of $L \otimes_K \mathbb{A}_{K,\infty}$ to the algebra norm over $\mathbb{A}_{K,\infty}$ of the underlying element of $t$, if and only if for every infinite place $w$ of $K$ the $w$-component $a_w$ of $a$ lies in the image of the corresponding map, sending a unit $t$ of $L \otimes_K K_w$ to the algebra norm over $K_w$ of the underlying element of $t$. Both ranges are ranges of norms of elements underlying units, not ranges of maps of unit groups.
--
--   This is the archimedean splitting of the local norm condition: being a norm from $(L \otimes_K \mathbb{A}_{K,\infty})^\times$ is equivalent to being a norm at each infinite place separately. It feeds the counting of places at which a given idele fails to be a local norm, used in the accompanying automorphic-form arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_mem_range_norm_tensorProduct_iff_forall_infinitePlace.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct

open scoped TensorProduct.RightActions in

theorem NumberField.InfiniteAdeleRing.mem_range_norm_tensorProduct_iff_forall_infinitePlace
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (a : (InfiniteAdeleRing K)ˣ) :
    ((a : InfiniteAdeleRing K) ∈ Set.range
        (fun t : (L ⊗[K] InfiniteAdeleRing K)ˣ => Algebra.norm (InfiniteAdeleRing K) (t : L ⊗[K] InfiniteAdeleRing K))) ↔
      ∀ w : InfinitePlace K,
        (a : InfiniteAdeleRing K) w ∈ Set.range
          (fun t : (L ⊗[K] w.Completion)ˣ => Algebra.norm w.Completion (t : L ⊗[K] w.Completion)) := by sorry
