-- Prove2me | Theorems.Thm_IharaLemma_smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one
-- name    : IharaLemma.smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/748e02ff-6669-51e2-90b7-1783a1f6036a
-- title:
--   Order-n residually trivial element acts trivially on a corner
-- statement:
--   Let $B$ be a commutative ring and let $M$ be a $B$-module (an additive commutative group with a $B$-module structure). Let $S$ be an idempotent splitting of $B$: data consisting of a natural number $n_S$, elements $e_0,\dots,e_{n_S-1}$ of $B$ forming a complete orthogonal family of idempotents, and ideals $\mathfrak m_0,\dots,\mathfrak m_{n_S-1}$, each maximal, such that every maximal ideal of $B$ occurs among the $\mathfrak m_j$ and such that $e_j \in \mathfrak m_k$ holds exactly when $j \neq k$. Fix an index $i$, an element $t \in B$ and a natural number $n$ such that the image of $n$ in $B$ is a unit, $t^n = 1$, and $t - 1 \in \mathfrak m_i$. Let $v$ be an element of the corner submodule attached to $e_i$, that is, of the range of the $B$-linear endomorphism $w \mapsto e_i \cdot w$ of $M$. Then $t \cdot v = v$.
--
--   A ring-theoretic triviality criterion of the kind used in the Taylor–Wiles auxiliary-level constructions: an element of finite order prime to the residue characteristic which is congruent to $1$ modulo a maximal ideal acts as the identity on the corresponding corner of any module. It is applied to diamond operators in a Hecke algebra acting on a cohomology group, through [`CohCarrier.diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem`](thm.html#CohCarrier.diamondL_apply_eq_self_of_mem_cornerSubmodule_of_sub_one_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaLemma_smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one.lean

import Definitions.Def_IharaLemma_IdempotentSplitting

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaLemma.smul_eq_self_of_mem_cornerSubmodule_of_pow_eq_one
    {B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
    (S : IharaLemma.IdempotentSplitting B) (i : Fin S.n) (t : B) (n : ℕ)
    (hn : IsUnit ((n : ℕ) : B)) (ht : t ^ n = 1) (h1 : t - 1 ∈ S.𝔪 i)
    (v : M) (hv : v ∈ IharaLemma.cornerSubmodule (M := M) (S.e i)) :
    t • v = v := by sorry
