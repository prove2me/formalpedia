-- Prove2me | Theorems.Thm_LinearMap_finrank_even_eq_finrank_odd_of_nineTerm_exact
-- name    : LinearMap.finrank_even_eq_finrank_odd_of_nineTerm_exact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/d5e9a5fe-d5a6-577a-a6d7-42fd3ebed652
-- title:
--   Euler characteristic of a nine-term exact sequence of k-vector spaces
-- statement:
--   Let $k$ be a field and let $V_0,\dots,V_8$ be $k$-vector spaces in a single universe, with $V_0,\dots,V_7$ finite-dimensional (no finiteness is assumed of $V_8$). Let $d_i : V_i \to V_{i+1}$, $0 \le i \le 7$, be $k$-linear maps, and assume: $\ker d_0 = 0$; $\operatorname{range} d_i = \ker d_{i+1}$ for each $i$ with $0 \le i \le 6$ (seven hypotheses, stated as equalities of submodules); and $\operatorname{range} d_7 = V_8$, i.e. the whole space. The conclusion is the identity of natural numbers $$\dim_k V_0 + \dim_k V_2 + \dim_k V_4 + \dim_k V_6 + \dim_k V_8 = \dim_k V_1 + \dim_k V_3 + \dim_k V_5 + \dim_k V_7,$$ with $\dim_k$ denoting `Module.finrank`. This is the subtraction-free form of the vanishing of the alternating sum $\sum_{i=0}^{8} (-1)^i \dim_k V_i$ for an exact sequence $0 \to V_0 \to \cdots \to V_8 \to 0$; the finiteness of $V_8$ needed for its dimension to be meaningful follows from the surjectivity of $d_7$.
--
--   This is the Euler-characteristic identity for an exact sequence of nine finite-dimensional vector spaces, arranged so that both sides are sums of natural numbers rather than an alternating sum. It is used in the project to compare even- and odd-position dimensions along a truncated long exact cohomology sequence, in [`groupCohomology.finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective`](thm.html#groupCohomology.finrank_euler_even_eq_odd_of_continuousH2MapHom_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_finrank_even_eq_finrank_odd_of_nineTerm_exact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem LinearMap.finrank_even_eq_finrank_odd_of_nineTerm_exact {k : Type u} [Field k]
    {V₀ V₁ V₂ V₃ V₄ V₅ V₆ V₇ V₈ : Type u}
    [AddCommGroup V₀] [Module k V₀] [AddCommGroup V₁] [Module k V₁]
    [AddCommGroup V₂] [Module k V₂] [AddCommGroup V₃] [Module k V₃]
    [AddCommGroup V₄] [Module k V₄] [AddCommGroup V₅] [Module k V₅]
    [AddCommGroup V₆] [Module k V₆] [AddCommGroup V₇] [Module k V₇]
    [AddCommGroup V₈] [Module k V₈]
    [FiniteDimensional k V₀] [FiniteDimensional k V₁] [FiniteDimensional k V₂]
    [FiniteDimensional k V₃] [FiniteDimensional k V₄] [FiniteDimensional k V₅]
    [FiniteDimensional k V₆] [FiniteDimensional k V₇]
    (d₀ : V₀ →ₗ[k] V₁) (d₁ : V₁ →ₗ[k] V₂) (d₂ : V₂ →ₗ[k] V₃) (d₃ : V₃ →ₗ[k] V₄)
    (d₄ : V₄ →ₗ[k] V₅) (d₅ : V₅ →ₗ[k] V₆) (d₆ : V₆ →ₗ[k] V₇) (d₇ : V₇ →ₗ[k] V₈)
    (e₀ : LinearMap.ker d₀ = ⊥)
    (e₁ : LinearMap.range d₀ = LinearMap.ker d₁) (e₂ : LinearMap.range d₁ = LinearMap.ker d₂)
    (e₃ : LinearMap.range d₂ = LinearMap.ker d₃) (e₄ : LinearMap.range d₃ = LinearMap.ker d₄)
    (e₅ : LinearMap.range d₄ = LinearMap.ker d₅) (e₆ : LinearMap.range d₅ = LinearMap.ker d₆)
    (e₇ : LinearMap.range d₆ = LinearMap.ker d₇) (e₈ : LinearMap.range d₇ = ⊤) :
    Module.finrank k V₀ + Module.finrank k V₂ + Module.finrank k V₄ + Module.finrank k V₆ + Module.finrank k V₈
      = Module.finrank k V₁ + Module.finrank k V₃ + Module.finrank k V₅ + Module.finrank k V₇ := by sorry
