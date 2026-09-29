-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_isClosed_range_prod_unitsAct_pow
-- name    : M4aHerbrand.IdeleGaloisDescent.isClosed_range_prod_unitsAct_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/400257db-b839-59d6-97f6-94e936842ade
-- title:
--   Closedness of the cyclic norm image in the idele group
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and an algebra over $K$, let $\sigma$ be a $K$-algebra automorphism of $L$, and let $D$ be a Galois descent datum for the adeles of $L$ over $K$, that is, a structure consisting of a monoid homomorphism $\mathrm{act}$ from the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-automorphisms of $L$ to the group of ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, together with the compatibility $\mathrm{act}(g)(\iota(x)) = \iota(g x)$ for every automorphism $g$ and every $x \in L$, where $\iota : L \to \mathbb{A}_L$ is the structure map, and the requirement that each $\mathrm{act}(g)$ be continuous. Each $\mathrm{act}(g)$ induces a multiplicative automorphism of the idele group $\mathbb{A}_L^{\times}$ by functoriality of units, written $D.\mathrm{unitsAct}(g)$. The assertion is that the image of the map
--   $$w \longmapsto \prod_{k=0}^{n-1} D.\mathrm{unitsAct}(\sigma^k)(w), \qquad n = \mathrm{orderOf}\ \sigma,$$
--   from $\mathbb{A}_L^{\times}$ to itself is a closed subset of $\mathbb{A}_L^{\times}$ in its topology as a unit group of the adele ring. No hypothesis is imposed on the order of $\sigma$; should $\sigma$ have infinite order, $n$ is $0$, the product is empty and the image is the singleton $\{1\}$.
--
--   When $\sigma$ generates a finite cyclic group with fixed field $F$, the displayed map is the idelic norm $N_{L/F} : \mathbb{A}_L^{\times} \to \mathbb{A}_F^{\times} \subseteq \mathbb{A}_L^{\times}$, and the statement is the closedness of the global norm group inside the idele group of $L$. It is used in the study of the adelic action of $\sigma$ on automorphic forms, where it feeds the construction of a compact set capturing central twists, via [`AutomorphicForm.exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul`](thm.html#AutomorphicForm.exists_isCompact_forall_exists_inv_mul_sigmaAdelicAct_mem_center_of_mem_center_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_isClosed_range_prod_unitsAct_pow.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.IdeleGaloisDescent.isClosed_range_prod_unitsAct_pow
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] (σ : L ≃ₐ[K] L)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) :
    IsClosed (Set.range fun w : (AdeleRing (𝓞 L) L)ˣ =>
      ∏ k ∈ Finset.range (orderOf σ), D.unitsAct (σ ^ k) w) := by sorry
