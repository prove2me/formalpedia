-- Prove2me | Theorems.Thm_ModularCurve_kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange
-- name    : ModularCurve.kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/06e98a0a-eae9-5f39-8c56-be2371000236
-- title:
--   Transport of the in-line divisibility under a Weierstrass variable change
-- statement:
--   Let $T$ be a commutative ring, $W$ a Weierstrass curve over $T$, and $C=(u,r,s,t)$ a Weierstrass variable change over $T$; let $\ell, d, n$ be natural numbers, $h \in T[X]$ and $x \in T$. Write $\mathrm{inLineMulPoly}\,W\,\ell\,n\,x_0$ for the polynomial $\prod_{a=1}^{\lfloor(\ell-1)/2\rfloor}\bigl(\Phi_n \cdot (\Psi^2_a)(x_0) - (\Phi_a)(x_0)\cdot \Psi^2_n\bigr) \in T[X]$, the product over $a$ in the interval $[1,(\ell-1)/2]$ of the differences of $\Phi_n$ times the constant $(\Psi^2_a)(x_0)$ and the constant $(\Phi_a)(x_0)$ times $\Psi^2_n$, where $\Phi_m$ and $\Psi^2_m$ are the division polynomials of the curve in question. Assume $h$ divides $\mathrm{inLineMulPoly}\,W\,\ell\,n\,x$. The conclusion is that $\mathrm{kernelVariableChangeDeg}\,C\,d\,h$, namely the polynomial $u^{-2d}\,h(u^{2}X + r)$ (the constant $u^{-2d}$ times the composition of $h$ with $u^{2}X+r$), divides $\mathrm{inLineMulPoly}\,(C \bullet W)\,\ell\,n\,\bigl(u^{-2}(x-r)\bigr)$, the corresponding polynomial for the transformed curve $C \bullet W$ evaluated at the transformed abscissa.
--
--   The statement records that the divisibility relation between a candidate kernel polynomial and the polynomial cutting out the abscissae of points whose $n$-th multiple lies on a prescribed line is invariant under changes of Weierstrass coordinates, with the kernel polynomial transported by $h \mapsto u^{-2d}h(u^{2}X+r)$. It is used to supply the coordinate-independence condition in the construction of the level moduli data attached to the curves with $\Gamma_1$-type level structure.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange.lean

import Mathlib
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.kernelVariableChangeDeg_dvd_inLineMulPoly_variableChange
    (T : Type u) [CommRing T] (W : WeierstrassCurve T) (C : WeierstrassCurve.VariableChange T)
    (ℓ d n : ℕ) (h : Polynomial T) (x : T)
    (hx : h ∣ ModularCurve.inLineMulPoly W ℓ n x) :
    ModularCurve.kernelVariableChangeDeg C d h ∣
      ModularCurve.inLineMulPoly (C • W) ℓ n (((C.u⁻¹ : Tˣ) : T) ^ 2 * (x - C.r)) := by sorry
