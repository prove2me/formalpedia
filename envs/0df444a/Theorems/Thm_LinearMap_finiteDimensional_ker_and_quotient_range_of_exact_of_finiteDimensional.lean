-- Prove2me | Theorems.Thm_LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional
-- name    : LinearMap.finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.015121+00:00
-- url     : https://prove2.me/theorems/3a7a08cd-e3be-536d-807c-eaf14ec9f1c7
-- title:
--   Finiteness of ker d₁ and coker d₁ in a ladder of two-term complexes
-- statement:
--   Let $k$ be a field and let $A_1,A_2,A_3,B_1,B_2,B_3$ be $k$-vector spaces (additive commutative groups with $k$-module structures, all in one universe). Given $k$-linear maps $d_1\colon A_1\to B_1$, $d_2\colon A_2\to B_2$, $d_3\colon A_3\to B_3$ and $f_1\colon A_1\to A_2$, $f_2\colon A_2\to A_3$, $g_1\colon B_1\to B_2$, $g_2\colon B_2\to B_3$, assume that $f_1$ is injective, that $f_1,f_2$ are exact at $A_2$ (the range of $f_1$ equals the kernel of $f_2$) and $f_2$ is surjective; likewise that $g_1$ is injective, that the range of $g_1$ equals the kernel of $g_2$, and that $g_2$ is surjective; so both rows are short exact sequences. Assume further that the ladder commutes, $g_1\circ d_1 = d_2\circ f_1$ and $g_2\circ d_2 = d_3\circ f_2$, as an equality of linear maps. Finally assume that $\ker d_2$, the quotient $B_2/\operatorname{range} d_2$, and $\ker d_3$ are finite-dimensional over $k$. The conclusion is that $\ker d_1$ is finite-dimensional over $k$ and that the quotient $B_1/\operatorname{range} d_1$ is finite-dimensional over $k$.
--
--   This is the finiteness half of the snake-lemma six-term exact sequence $0\to\ker d_1\to\ker d_2\to\ker d_3\to\operatorname{coker} d_1\to\operatorname{coker} d_2\to\operatorname{coker} d_3\to 0$ attached to a short exact sequence of two-term complexes: finiteness for the middle complex together with finiteness of $\ker d_3$ propagates to the sub-complex. It is used in the bounding of Euler characteristics of spaces of sections in the curve-theoretic part of the development, namely by [`AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing`](thm.html#AlgebraicGeometry.eulerChar_sectionsOf_le_one_sub_genusFF_sub_natCard_not_isRegularLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LinearMap_finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem LinearMap.finiteDimensional_ker_and_quotient_range_of_exact_of_finiteDimensional
    {k : Type u} [Field k]
    {A₁ A₂ A₃ B₁ B₂ B₃ : Type v}
    [AddCommGroup A₁] [Module k A₁] [AddCommGroup A₂] [Module k A₂] [AddCommGroup A₃] [Module k A₃]
    [AddCommGroup B₁] [Module k B₁] [AddCommGroup B₂] [Module k B₂] [AddCommGroup B₃] [Module k B₃]
    (d₁ : A₁ →ₗ[k] B₁) (d₂ : A₂ →ₗ[k] B₂) (d₃ : A₃ →ₗ[k] B₃)
    (f₁ : A₁ →ₗ[k] A₂) (f₂ : A₂ →ₗ[k] A₃) (g₁ : B₁ →ₗ[k] B₂) (g₂ : B₂ →ₗ[k] B₃)
    (hf₁ : Function.Injective f₁) (hf : Function.Exact f₁ f₂) (hf₂ : Function.Surjective f₂)
    (hg₁ : Function.Injective g₁) (hg : Function.Exact g₁ g₂) (hg₂ : Function.Surjective g₂)
    (h₁ : g₁ ∘ₗ d₁ = d₂ ∘ₗ f₁) (h₂ : g₂ ∘ₗ d₂ = d₃ ∘ₗ f₂)
    [FiniteDimensional k (LinearMap.ker d₂)] [FiniteDimensional k (B₂ ⧸ LinearMap.range d₂)]
    [FiniteDimensional k (LinearMap.ker d₃)] :
    FiniteDimensional k (LinearMap.ker d₁) ∧ FiniteDimensional k (B₁ ⧸ LinearMap.range d₁) := by sorry
