-- Prove2me | Theorems.Thm_ModularCurve_sum_periodOf_mul_edgeIntegral_eq_zero
-- name    : ModularCurve.sum_periodOf_mul_edgeIntegral_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/85cf79ea-7a4c-5ebd-b56f-42bfb522eb3c
-- title:
--   Vanishing twisted edge sum: the (2,0) bilinear relation on X_Γ
-- statement:
--   Let $\Gamma$ be a finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$ containing $-1$ and with finite coset space $\mathrm{SL}_2(\mathbb Z)/\Gamma$, and let $k,g$ be weight-$2$ cusp forms for $\Gamma$. Let $\gamma_T,\gamma_S$ assign to each coset $q$ an element of $\Gamma$, subject to $\gamma_T(q)=\sigma_{Tq}^{-1}T\sigma_q$ and $\gamma_S(q)=\sigma_{Sq}^{-1}S\sigma_q$ inside $\mathrm{SL}_2(\mathbb Z)$, where $\sigma_q$ denotes the chosen representative `Quotient.out q` and $T,S$ are `ModularGroup.T`, `ModularGroup.S`. Let $G$ assign to each $q$ the function on $\mathbb C$ given by $G_q(z)=g(\sigma_q^{-1}\cdot \mathrm{ofComplex}\,z)/\mathrm{denom}(\sigma_q^{-1},\mathrm{ofComplex}\,z)^2$, the weight-$2$ slash of $g$ by $\sigma_q^{-1}$ read as a function of a complex variable. Writing $P_k(\gamma)=\mathrm{periodOf}\,\Gamma\,\gamma\,k=\int_0^1 \mathrm{periodIntegrandOf}\,\Gamma\,i\,(\gamma\cdot i)\,k$, the period of $k$ along the path from $i$ to $\gamma\cdot i$, the conclusion is the identity
--   $$i\sum_{q}P_k(\gamma_T(q))\int_{\sqrt3/2}^{\infty}G_q\bigl(-\tfrac12+iy\bigr)\,dy\;+\;\tfrac12\sum_{q}P_k(\gamma_S(q))\int_{\pi/3}^{2\pi/3}G_q(e^{i\theta})\,ie^{i\theta}\,d\theta\;=\;0,$$
--   the sums being over all cosets $q\in\mathrm{SL}_2(\mathbb Z)/\Gamma$.
--
--   This is Riemann's bilinear relation of type $(2,0)$ for the modular curve $X_\Gamma$, written out explicitly on the tiling of a fundamental set for $\Gamma$ by translates of the standard fundamental domain of $\mathrm{SL}_2(\mathbb Z)$: the twisted sums of the left-edge and bottom-arc integrals of $g$, weighted by the periods of $k$, cancel. It is used, together with the companion $(1,1)$ relation, in [`ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int`](thm.html#ModularCurve.petersson_mem_periodLatticeOf_iff_re_periodOf_int), which characterises membership of a Petersson product in the period lattice through the real parts of the periods of $k$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_sum_periodOf_mul_edgeIntegral_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_PeriodOf
import Definitions.Def_AutomorphicForm_Gamma0FundamentalSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UpperHalfPlane MeasureTheory
open scoped MatrixGroups Topology ComplexConjugate

theorem ModularCurve.sum_periodOf_mul_edgeIntegral_eq_zero
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hneg : (-1 : SL(2, ℤ)) ∈ Γ)
    [Fintype (SL(2, ℤ) ⧸ Γ)]
    (k g : CuspForm Γ 2)
    (γT γS : SL(2, ℤ) ⧸ Γ → Γ)
    (hT : ∀ q, ((γT q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.T • q))⁻¹ * ModularGroup.T * Quotient.out q)
    (hS : ∀ q, ((γS q : Γ) : SL(2, ℤ)) =
      (Quotient.out (ModularGroup.S • q))⁻¹ * ModularGroup.S * Quotient.out q)
    (G : SL(2, ℤ) ⧸ Γ → ℂ → ℂ)
    (hG : ∀ q z, G q z = g ((Quotient.out q)⁻¹ • ofComplex z) /
      denom (((Quotient.out q)⁻¹ : SL(2, ℤ)) : GL (Fin 2) ℝ) (ofComplex z) ^ 2) :
    Complex.I * ∑ q : SL(2, ℤ) ⧸ Γ,
          ModularCurve.periodOf Γ (γT q) k *
            (∫ y in Set.Ioi (Real.sqrt 3 / 2), G q (-(1 / 2) + y * Complex.I)) +
        1 / 2 * ∑ q : SL(2, ℤ) ⧸ Γ,
          ModularCurve.periodOf Γ (γS q) k *
            (∫ θ in (Real.pi / 3)..(2 * Real.pi / 3),
              G q (Complex.exp (θ * Complex.I)) * (Complex.I * Complex.exp (θ * Complex.I))) = 0 := by sorry
