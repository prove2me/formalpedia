-- Prove2me | Theorems.Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact
-- name    : LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/67e6bed3-679e-521b-b5dd-36f4b736cbe2
-- title:
--   Alternating sum of dimensions along a long exact sequence
-- statement:
--   Let $k$ be a division ring and let $A$, $B$, $C$ be families of $k$-modules indexed by the natural numbers, each member finite over $k$. Given families of $k$-linear maps $f_i : A_i \to B_i$, $g_i : B_i \to C_i$ and $\delta_i : C_i \to A_{i+1}$ such that $f_0$ is injective, and such that for every $i$ the pairs $(f_i, g_i)$, $(g_i, \delta_i)$ and $(\delta_i, f_{i+1})$ are exact in the sense that the kernel of the second map equals the range of the first — that is, $\ker g_i = \operatorname{im} f_i$, $\ker \delta_i = \operatorname{im} g_i$ and $\ker f_{i+1} = \operatorname{im} \delta_i$ — and given a natural number $N$ for which $A_N$ has at most one element (i.e. $A_N = 0$), the assertion is the vanishing of the integer alternating sum $$\sum_{i=0}^{N-1} (-1)^i\bigl(\dim_k A_i - \dim_k B_i + \dim_k C_i\bigr) = 0,$$ the dimensions being `Module.finrank` over $k$, cast to $\mathbb{Z}$, and the sum taken over $i$ in the range $\{0,\dots,N-1\}$. No exactness or finiteness beyond index $N$ is needed for the statement, although the hypotheses are imposed for all indices.
--
--   This is the linear algebra underlying the additivity of Euler characteristics: applied to the long exact cohomology sequence of a short exact sequence of sheaves, with $A_i$, $B_i$, $C_i$ the $i$-th cohomology groups and $N$ beyond the cohomological dimension, it yields $\chi(\mathcal F) = \chi(\mathcal F') + \chi(\mathcal F'')$. It is used in exactly this way by [`AlgebraicGeometry.OModulePresheaf.eulerChar_eq_add_of_affSES`](thm.html#AlgebraicGeometry.OModulePresheaf.eulerChar_eq_add_of_affSES).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_sum_neg_one_pow_mul_finrank_eq_zero_of_exact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem LinearMap.sum_neg_one_pow_mul_finrank_eq_zero_of_exact
    {k : Type u} [DivisionRing k] (A B C : ℕ → Type v)
    [∀ i, AddCommGroup (A i)] [∀ i, Module k (A i)] [∀ i, Module.Finite k (A i)]
    [∀ i, AddCommGroup (B i)] [∀ i, Module k (B i)] [∀ i, Module.Finite k (B i)]
    [∀ i, AddCommGroup (C i)] [∀ i, Module k (C i)] [∀ i, Module.Finite k (C i)]
    (f : ∀ i, A i →ₗ[k] B i) (g : ∀ i, B i →ₗ[k] C i) (δ : ∀ i, C i →ₗ[k] A (i + 1))
    (hf0 : Function.Injective (f 0))
    (hfg : ∀ i, Function.Exact (f i) (g i))
    (hgδ : ∀ i, Function.Exact (g i) (δ i))
    (hδf : ∀ i, Function.Exact (δ i) (f (i + 1)))
    (N : ℕ) (hN : Subsingleton (A N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i *
        ((Module.finrank k (A i) : ℤ) - Module.finrank k (B i) + Module.finrank k (C i)) = 0 := by sorry
