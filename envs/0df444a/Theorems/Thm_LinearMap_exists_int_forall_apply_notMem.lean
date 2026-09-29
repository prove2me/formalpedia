-- Prove2me | Theorems.Thm_LinearMap_exists_int_forall_apply_notMem
-- name    : LinearMap.exists_int_forall_apply_notMem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/8a46c34f-9781-551d-87e0-7f2c8809654f
-- title:
--   Integer points avoiding finitely many linear conditions
-- statement:
--   Let $K$ be a field of characteristic zero, let $V$ be a $K$-vector space, let $r$ be a natural number and let $\iota$ be an arbitrary index type. Given a finite set $S \subseteq \iota$, a family of $K$-linear maps $f_t \colon K^r \to V$ indexed by $t \in \iota$ (where $K^r$ is the space of functions $\mathrm{Fin}\ r \to K$), and a family of $K$-submodules $W_t \subseteq V$, assume that each condition can be avoided separately over $K$: for every $t \in S$ there exists $c \in K^r$ with $f_t(c) \notin W_t$. The conclusion is that a single integral vector avoids all the conditions at once, namely there exists $c \colon \mathrm{Fin}\ r \to \mathbb{Z}$ such that, writing $\iota \mapsto (c_i : K)$ for the componentwise image of $c$ in $K^r$ under the canonical ring map $\mathbb{Z} \to K$, one has $f_t\big((c_i)_i\big) \notin W_t$ for every $t \in S$. No hypothesis is placed on $t \notin S$.
--
--   An elementary characteristic-zero Zariski-density statement: each hypothesis says that the preimage $f_t^{-1}(W_t)$ is a proper subspace of $K^r$, and the conclusion is that the integral lattice points are not covered by finitely many such proper subspaces. It is used in the construction of functions on $X_0(N)$ with prescribed order of vanishing and nonvanishing derivative, being cited by [`ModularCurve.JZero.exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero`](thm.html#ModularCurve.JZero.exists_forall_exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero) and [`ModularCurve.JZero.exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero`](thm.html#ModularCurve.JZero.exists_ord_sub_evalAt_eq_one_and_derivative_evalEval_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_exists_int_forall_apply_notMem.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LinearMap.exists_int_forall_apply_notMem
    {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {r : ℕ} {ι : Type*}
    (S : Finset ι) (f : ι → (Fin r → K) →ₗ[K] V) (W : ι → Submodule K V)
    (h : ∀ t ∈ S, ∃ c : Fin r → K, f t c ∉ W t) :
    ∃ c : Fin r → ℤ, ∀ t ∈ S, f t (fun i => (c i : K)) ∉ W t := by sorry
