-- Prove2me | Theorems.Thm_IharaTower_RungAssembly_map_delta_of_sq_sub
-- name    : IharaTower.RungAssembly.map_delta_of_sq_sub
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/4e561cf5-17c3-587f-ac3a-f0c542d91528
-- title:
--   Rung Δ-value from the unit-root quadratic relation
-- statement:
--   Let $\mathcal{O}$ be a commutative ring, $T$ a commutative $\mathcal{O}$-algebra, and $\pi_T \colon T \to \mathcal{O}$ an $\mathcal{O}$-algebra homomorphism. Let $a, t, \Delta \in T$ and let $p, n_u, n_l, n_q, n_1$ be natural numbers subject to $n_u = 1$, $n_l = 1$, $n_q = p + 1$ and $n_1 = p + 1$. Assume the quadratic relation $a\cdot a - t\cdot a + p\cdot 1 = 0$ in $T$, the natural number $p$ being mapped into $T$ through $\mathcal{O}$ by the structure map, and assume that $\Delta$ is given by the expression $$\Delta = a^2\,(n_u\, t) - a\,(n_q + n_1) + n_l\, t,$$ again with the integers $n_u, n_q, n_1, n_l$ taken as images of natural numbers in $T$ via $\mathcal{O}$. Then the value of $\pi_T$ on $\Delta$ satisfies $$\pi_T(\Delta) = \bigl(\pi_T(a) - \pi_T(t - a)\bigr)\bigl(\pi_T(a)^2 - 1\bigr).$$ Thus, writing $\alpha = \pi_T(a)$ and $\beta = \pi_T(t-a)$ for the two roots attached to the relation, the specialisation of $\Delta$ is $(\alpha - \beta)(\alpha^2 - 1)$.
--
--   This is the $\eta$-type computation attached to a rung of the two-leg tower table, in which both Hecke slots carry the same element $t$ and $a$ plays the role of the unit root of the $p$-th Hecke polynomial, so that $\pi_T(a)$ and $\pi_T(t-a)$ are the two roots with product $p$. It is used in the construction of a Hecke-module rung at the residue characteristic via the unit root, in [`CuspForm.heckeLocal.exists_heckeModule_rung_at_residueChar_unitRoot_of_cornerData_of_fullCorner_of_not_cube_dvd`](thm.html#CuspForm.heckeLocal.exists_heckeModule_rung_at_residueChar_unitRoot_of_cornerData_of_fullCorner_of_not_cube_dvd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IharaTower_RungAssembly_map_delta_of_sq_sub.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IharaTower.RungAssembly.map_delta_of_sq_sub {𝒪 : Type} [CommRing 𝒪] {T : Type} [CommRing T] [Algebra 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (a t Δ : T) (p nu nl nq n1 : ℕ)
    (hnu : nu = 1) (hnl : nl = 1) (hnq : nq = p + 1) (hn1 : n1 = p + 1)
    (hαq : a * a - t * a + algebraMap 𝒪 T (p : 𝒪) = 0)
    (hΔ : Δ = a ^ 2 * (algebraMap 𝒪 T (nu : 𝒪) * t) - a * (algebraMap 𝒪 T (nq : 𝒪) + algebraMap 𝒪 T (n1 : 𝒪))
        + algebraMap 𝒪 T (nl : 𝒪) * t) :
    πT Δ = (πT a - πT (t - a)) * (πT a ^ 2 - 1) := by sorry
