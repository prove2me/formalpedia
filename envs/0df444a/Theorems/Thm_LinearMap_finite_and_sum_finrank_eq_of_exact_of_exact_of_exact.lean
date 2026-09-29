-- Prove2me | Theorems.Thm_LinearMap_finite_and_sum_finrank_eq_of_exact_of_exact_of_exact
-- name    : LinearMap.finite_and_sum_finrank_eq_of_exact_of_exact_of_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/758ce91f-e271-5173-9f2b-a788699e34b4
-- title:
--   Additivity of Euler characteristic along a long exact sequence
-- statement:
--   Let $k$ be a field and let $A$, $B$, $Q$ be families of $k$-vector spaces indexed by $\mathbb{N}$ (all in one universe), equipped with $k$-linear maps $f_n : A_n \to B_n$, $g_n : B_n \to Q_n$ and $\delta_n : Q_n \to A_{n+1}$ for every $n$. Assume exactness at each spot: $\operatorname{range}(f_n) = \ker(g_n)$, $\operatorname{range}(g_n) = \ker(\delta_n)$ and $\operatorname{range}(\delta_n) = \ker(f_{n+1})$ for all $n$; assume further that every $A_n$ and every $Q_n$ is a finite $k$-module, i.e. finite-dimensional. Let $M \in \mathbb{N}$ be such that $f_0$ and $f_M$ are injective. Then two conclusions hold: every $B_n$ is finite-dimensional over $k$, and the alternating sums of dimensions over $n < M$ satisfy, as an identity in $\mathbb{Z}$, $$\sum_{n<M} (-1)^n \dim_k B_n = \sum_{n<M} (-1)^n \dim_k A_n + \sum_{n<M} (-1)^n \dim_k Q_n.$$ Note that finiteness of the $B_n$ is asserted for all $n$, not merely for $n < M$, and that the truncation bound $M$ enters only through the injectivity of $f_0$ and $f_M$.
--
--   This is the additivity of the Euler characteristic along a long exact sequence of finite-dimensional vector spaces, in the shape of a three-term periodic exact sequence truncated at a degree $M$ where the connecting data degenerates. It is used in the computation of dimensions of total cohomology of a double complex, by [`DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift`](thm.html#DoubleComplex.finite_HTot_and_sum_finrank_HTot_eq_sub_of_rowShift).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_finite_and_sum_finrank_eq_of_exact_of_exact_of_exact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem LinearMap.finite_and_sum_finrank_eq_of_exact_of_exact_of_exact
    {k : Type u} [Field k] (A B Q : ℕ → Type u)
    [∀ n, AddCommGroup (A n)] [∀ n, Module k (A n)] [∀ n, AddCommGroup (B n)] [∀ n, Module k (B n)]
    [∀ n, AddCommGroup (Q n)] [∀ n, Module k (Q n)]
    (f : ∀ n, A n →ₗ[k] B n) (g : ∀ n, B n →ₗ[k] Q n) (δ : ∀ n, Q n →ₗ[k] A (n + 1))
    (hfg : ∀ n, LinearMap.range (f n) = LinearMap.ker (g n))
    (hgδ : ∀ n, LinearMap.range (g n) = LinearMap.ker (δ n))
    (hδf : ∀ n, LinearMap.range (δ n) = LinearMap.ker (f (n + 1)))
    (hA : ∀ n, Module.Finite k (A n)) (hQ : ∀ n, Module.Finite k (Q n))
    (M : ℕ) (hf0 : Function.Injective (f 0)) (hfM : Function.Injective (f M)) :
    (∀ n, Module.Finite k (B n)) ∧
      ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (B n) : ℤ) =
        ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (A n) : ℤ) +
          ∑ n ∈ Finset.range M, (-1 : ℤ) ^ n * (Module.finrank k (Q n) : ℤ) := by sorry
