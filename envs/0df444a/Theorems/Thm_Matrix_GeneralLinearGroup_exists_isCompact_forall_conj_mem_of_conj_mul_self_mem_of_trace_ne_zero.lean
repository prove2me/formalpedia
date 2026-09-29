-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero
-- name    : Matrix.GeneralLinearGroup.exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/f58ca46e-0af7-576a-9e42-d808ca55689a
-- title:
--   Compact bound on conjugates of t from conjugates of t²
-- statement:
--   Let $\mathbb{k}$ be an `RCLike` field (so $\mathbb{R}$ or $\mathbb{C}$), and work in the group $GL_2(\mathbb{k})$ of units of the ring of $2\times 2$ matrices over $\mathbb{k}$, with its usual topology. Let $T \subseteq GL_2(\mathbb{k})$ be a compact set all of whose elements $t$ have non-zero trace, that is, the trace of the underlying matrix of $t$ is non-zero for every $t \in T$, and let $B \subseteq GL_2(\mathbb{k})$ be any compact set. The assertion is that there exists a compact set $B' \subseteq GL_2(\mathbb{k})$ such that for every $t \in T$ and every $x \in GL_2(\mathbb{k})$, if $x^{-1}(t\cdot t)x \in B$ then $x^{-1}tx \in B'$. Thus $B'$ depends only on $T$ and $B$, uniformly in $t$ and $x$; no compactness or other restriction is placed on the set of admissible $x$.
--
--   This is the $GL_2$ case of the elementary step in Harish-Chandra's uniform properness arguments near a central element: control of conjugates of $t$ by conjugates of $t^2$. It is used in the construction of neighbourhoods controlling twisted conjugation, by [`AutomorphicForm.exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg`](thm.html#AutomorphicForm.exists_nhds_isCompact_forall_twistedCentralizer_conjAe_mul_mem_of_neg) and [`AutomorphicForm.exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem`](thm.html#AutomorphicForm.exists_nhds_one_forall_isCompact_exists_eq_toTensorGL_mul_of_conjAe_twistedConj_mem), typically with $T$ a compact neighbourhood of the identity, where the trace is close to $2$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_GeneralLinearGroup_exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.exists_isCompact_forall_conj_mem_of_conj_mul_self_mem_of_trace_ne_zero
    {𝕜 : Type*} [RCLike 𝕜]
    (T : Set (GL (Fin 2) 𝕜)) (hT : IsCompact T)
    (hTtr : ∀ t ∈ T, Matrix.trace ((t : GL (Fin 2) 𝕜) : Matrix (Fin 2) (Fin 2) 𝕜) ≠ 0)
    (B : Set (GL (Fin 2) 𝕜)) (hB : IsCompact B) :
    ∃ B' : Set (GL (Fin 2) 𝕜), IsCompact B' ∧
      ∀ t ∈ T, ∀ x : GL (Fin 2) 𝕜, x⁻¹ * (t * t) * x ∈ B → x⁻¹ * t * x ∈ B' := by sorry
