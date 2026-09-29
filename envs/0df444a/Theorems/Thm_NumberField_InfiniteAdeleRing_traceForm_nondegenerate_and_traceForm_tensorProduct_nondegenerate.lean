-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate
-- name    : NumberField.InfiniteAdeleRing.traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/b0219b8d-470d-5292-ba6d-f9a7d1df4b5a
-- title:
--   Nondegeneracy of the real trace forms on K_∞ and L⊗_K K_∞
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$. The infinite adele ring $\mathbb{A}_{K,\infty}$ (`InfiniteAdeleRing K`, the product of the archimedean completions of $K$) is given the structure of an $\mathbb{R}$-algebra by transporting the canonical $\mathbb{R}$-algebra structure of the mixed space $\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$ along the inverse of the ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace K`; the $K$-algebra $L\otimes_K \mathbb{A}_{K,\infty}$ is then given the $\mathbb{R}$-algebra structure obtained by following this structure map with the right inclusion $a\mapsto 1\otimes a$ of $\mathbb{A}_{K,\infty}$ into the tensor product. With respect to these structures the assertion is the conjunction of two statements: the $\mathbb{R}$-bilinear trace form $(x,y)\mapsto \operatorname{Tr}_{\mathbb{A}_{K,\infty}/\mathbb{R}}(xy)$ on $\mathbb{A}_{K,\infty}$ is nondegenerate, and the $\mathbb{R}$-bilinear trace form $(x,y)\mapsto \operatorname{Tr}_{(L\otimes_K \mathbb{A}_{K,\infty})/\mathbb{R}}(xy)$ on $L\otimes_K \mathbb{A}_{K,\infty}$ is nondegenerate; nondegeneracy here means that an element pairing to zero with every element is zero.
--
--   This is the statement that the finite-dimensional commutative real algebras $K_\infty=\prod_{v\mid\infty}K_v$ and $L\otimes_K K_\infty$ are separable (étale), expressed through the nonvanishing of their trace pairings. It is used in the construction of archimedean Haar measures for automorphic forms, where it supplies the self-duality needed to compare a Haar measure on $L\otimes_K K_\infty$ with a density against a measure transported from $K_\infty$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField
open scoped TensorProduct TensorProduct.RightActions

theorem NumberField.InfiniteAdeleRing.traceForm_nondegenerate_and_traceForm_tensorProduct_nondegenerate
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    letI : Algebra ℝ (InfiniteAdeleRing K) :=
      ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm.toRingHom.comp
        (algebraMap ℝ (mixedEmbedding.mixedSpace K))).toAlgebra
    letI : Algebra ℝ (L ⊗[K] InfiniteAdeleRing K) :=
      ((Algebra.TensorProduct.includeRight : InfiniteAdeleRing K →ₐ[K] L ⊗[K] InfiniteAdeleRing K).toRingHom.comp
        (algebraMap ℝ (InfiniteAdeleRing K))).toAlgebra
    (Algebra.traceForm ℝ (InfiniteAdeleRing K)).Nondegenerate ∧
      (Algebra.traceForm ℝ (L ⊗[K] InfiniteAdeleRing K)).Nondegenerate := by sorry
