-- Prove2me | Theorems.Thm_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne
-- name    : Matrix.SpecialLinearGroup.finrank_addMonoidHom_eq_of_forall_trace_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/245dc773-3bfc-5c53-b085-126353660e5b
-- title:
--   Dimension of Hom(Γ,K) for elliptic-free ΓleSL₂(ℤ)
-- statement:
--   Let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb Z)$ (the group of $2\times 2$ integer matrices of determinant $1$) of finite index, and assume that $-1\in\Gamma$ and that every $\gamma\in\Gamma$ has $\operatorname{tr}(\gamma)\neq 0$, $\operatorname{tr}(\gamma)\neq 1$ and $\operatorname{tr}(\gamma)\neq -1$, the trace being taken of the underlying integer matrix. Let $K$ be a field of characteristic zero. Then the $K$-vector space $\mathrm{Hom}(\Gamma,K)$ of additive characters of $\Gamma$ — formally, the additive monoid homomorphisms from $\Gamma$, viewed additively via `Additive`, to $K$, with its $K$-module structure by scaling in the target — has finite dimension, and $$\dim_K\mathrm{Hom}(\Gamma,K) = 1 + [\mathrm{SL}_2(\mathbb Z):\Gamma]/6,$$ where the quotient is division of natural numbers (truncated); the index is `Subgroup.index`. The assertion is about `Module.finrank`, so it simultaneously records that the dimension is finite and equal to the stated value.
--
--   The hypothesis on traces excludes elements of finite order other than $\pm 1$, so the image $\bar\Gamma$ of $\Gamma$ in $\mathrm{PSL}_2(\mathbb Z)$ is free of rank $1 + [\mathrm{SL}_2(\mathbb Z):\Gamma]/6$; this statement converts that freeness into the dimension of the space of $K$-valued characters, i.e. of $H^1(\Gamma,K)$ with trivial action. It feeds the count of parabolic homomorphisms on $\Gamma$ used in the numerics of modular curves, being cited by [`ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq`](thm.html#ModularCurve.six_mul_level_mul_finrank_parabolicHoms_Gamma_add_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_SpecialLinearGroup_finrank_addMonoidHom_eq_of_forall_trace_ne.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Matrix.SpecialLinearGroup.finrank_addMonoidHom_eq_of_forall_trace_ne
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex]
    (hneg : (-1 : Matrix.SpecialLinearGroup (Fin 2) ℤ) ∈ Γ)
    (hΓ : ∀ γ ∈ Γ, (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 0 ∧
      (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ 1 ∧ (γ : Matrix (Fin 2) (Fin 2) ℤ).trace ≠ -1)
    (K : Type) [Field K] [CharZero K] :
    Module.finrank K (Additive Γ →+ K) = 1 + Γ.index / 6 := by sorry
