-- Prove2me | Theorems.Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
-- name    : IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/cab14a4f-47e2-53bc-93bb-8c8a5b3e076c
-- title:
--   Uniform local constancy of compactly supported locally constant functions
-- statement:
--   Let $G$ be a group carrying a topology for which it is a topological group, let $M$ be a type with a distinguished element $0$, and let $\Phi : G \to M$ be a function that is locally constant (the preimage of every subset of $M$ is open) and has compact support, i.e. the closure of $\{g : \Phi(g) \neq 0\}$ is compact. The assertion is that there exists a subset $W \subseteq G$ which is open, contains the identity $1$, and is such that for every $g \in G$ and every $w \in W$ one has both $\Phi(g w) = \Phi(g)$ and $\Phi(w g) = \Phi(g)$. Thus the local constancy of $\Phi$ is uniform: a single neighbourhood $W$ of $1$ works simultaneously for all $g$, on both sides. No separation or local compactness hypothesis on $G$ is imposed, and $M$ carries no structure beyond a point called $0$.
--
--   This is the standard uniform smoothness property of compactly supported locally constant ("test") functions on a topological group: such a function is invariant under translation by a fixed neighbourhood of the identity. It serves as the basic uniformity input for the analysis of local test functions and weighted orbital integrals, and is invoked by the lemmas on half-weighted orbital integrals that require a single neighbourhood of $1$ independent of the point of $G$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocallyConstant_exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocallyConstant.exists_isOpen_one_mem_forall_mul_eq_of_hasCompactSupport
    {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Zero M]
    (Φ : G → M) (hlc : IsLocallyConstant Φ) (hcs : HasCompactSupport Φ) :
    ∃ W : Set G, IsOpen W ∧ (1 : G) ∈ W ∧
      ∀ g : G, ∀ w ∈ W, Φ (g * w) = Φ g ∧ Φ (w * g) = Φ g := by sorry
