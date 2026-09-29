-- Prove2me | Theorems.Thm_LinearMap_exists_int_forall_apply_ne
-- name    : LinearMap.exists_int_forall_apply_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/b2ac9fc4-82c3-58c9-ae93-5fa519e2d289
-- title:
--   Integer points avoiding finitely many affine hyperplanes
-- statement:
--   Let $K$ be a field of characteristic zero, let $r$ be a natural number and let $\iota$ be an arbitrary index type. Given a finite subset $S \subseteq \iota$, a family $f : \iota \to ((\mathrm{Fin}\ r \to K) \to_{K} K)$ of $K$-linear functionals on the coordinate space $K^{r}$, and a family $a : \iota \to K$ of scalars, assume that $f_j \neq 0$ for every $j \in S$ (no condition is imposed on $f_j$ or $a_j$ for $j \notin S$). Then there exists an integer vector $c : \mathrm{Fin}\ r \to \mathbb{Z}$ such that for every $j \in S$ one has $f_j\bigl(i \mapsto (c_i : K)\bigr) \neq a_j$, the integer entries being mapped into $K$ by the canonical ring homomorphism $\mathbb{Z} \to K$. Equivalently: the image of $\mathbb{Z}^{r}$ in $K^{r}$ is not covered by the finitely many affine hyperplanes $\{f_j = a_j\}$, $j \in S$.
--
--   This is the elementary avoidance statement that finitely many affine hyperplanes in $K^{r}$, $K$ of characteristic zero, never contain the whole integer lattice; characteristic zero enters only through the injectivity of $\mathbb{Z} \to K$. It is used in the form [`LinearMap.exists_int_forall_apply_notMem`](thm.html#LinearMap.exists_int_forall_apply_notMem) and, further downstream, in the constructions of functions on modular curves with prescribed order of vanishing and non-vanishing derivative.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_int_forall_apply_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.exists_int_forall_apply_ne {K : Type*} [Field K] [CharZero K] {r : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → (Fin r → K) →ₗ[K] K) (a : ι → K) (hf : ∀ j ∈ S, f j ≠ 0) :
    ∃ c : Fin r → ℤ, ∀ j ∈ S, f j (fun i => (c i : K)) ≠ a j := by sorry
