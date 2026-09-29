-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_AuxLevel_levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
-- name    : ModularCurve.FullLevel.AuxLevel.levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:22.181174+00:00
-- url     : https://prove2.me/theorems/e21416a6-914a-5f20-889c-49bbfb74d545
-- title:
--   Transport of twisted Tate torsion coordinates by a level automorphism
-- statement:
--   Let $q\ge 5$ and $\ell\ge 3$ be distinct primes, $M'$ a nonzero natural number divisible by neither, $L$ a field of characteristic zero, $\xi\in L$ a primitive $(q\ell)$-th root of unity, and $\iota : L\to\mathbb{C}$ a ring homomorphism with $\iota\xi=\exp(2\pi i/(q\ell))$; write $\xi_u$ for $\xi$ viewed as a unit. Let $K$ be the intermediate field of $L\subseteq \mathrm{LaurentSeries}\,L$ obtained by adjoining to $L$ the coefficientwise image of the $q$-expansion function field of $\Gamma_H$ at level $(q\ell)^2M'$, $H$ being the kernel of reduction $(\mathbb{Z}/(q\ell)^2M')^\times\to(\mathbb{Z}/q\ell)^\times$. Let $\gamma\in\mathrm{SL}_2(\mathbb{Z})$ lie in $\Gamma_0(M')$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for $\gamma^{-1}$, i.e. for all weights $k$, all forms $f,g$ of weight $k$ on $\Gamma_H((q\ell)^2M')$ with integral $q$-expansions and $g$'s expansion nonzero, and all $x\in K$ whose Laurent series is the image of $f/g$'s $q$-expansion quotient, one has $\iota$-coefficientwise $\tau x\cdot (g\mid_k \mathrm{conjElemN}(q\ell,\gamma^{-1}))=f\mid_k \mathrm{conjElemN}(q\ell,\gamma^{-1})$ as $q$-expansions. Write $(x_v,y_v)=$ [`ModularCurve.cuspPoint`](def/ModularCurve_KatzLevelPCusps.html#L59) $L\,(q\ell)\,\xi_u\,v$, the Tate-curve coordinate pair attached to $v\in(\mathbb{Z}/q\ell)^2$ (toric series when $v_1=0$, non-toric slot series otherwise), and set $w_0=(1,0)$, $w_0\sigma=(\gamma_{00},-\gamma_{10})$. Assume a variable change $C_0$ over $\mathrm{LaurentSeries}\,L$ with $u_0\,(2x_{w_0}+\tfrac16)=2y_{w_0}+x_{w_0}$, $r_0=-\tfrac1{12}$, $s_0=-\tfrac12$, $t_0=\tfrac1{24}$, and a unit $\mu$ of $K$ with $\mu\,(2y_{w_0\sigma}+x_{w_0\sigma})\cdot 2(x_{w_0}+\tfrac1{12})=(2y_{w_0}+x_{w_0})\cdot 2(x_{w_0\sigma}+\tfrac1{12})$. Finally let $v\neq 0$, put $v\sigma=(\gamma_{00}v_0-\gamma_{01}v_1,\,-\gamma_{10}v_0+\gamma_{11}v_1)$, and let $X,Y,X',Y'\in K$ have Laurent series $u_0^{-2}(x_v-r_0)$, $u_0^{-3}(y_v-s_0(x_v-r_0)-t_0)$ and the same expressions for $v\sigma$. Then $\tau X=\mu^2X'$ and $\tau Y=\mu^3Y'$.
--
--   This is the single-torsion-point core of the coordinate-transport step: the automorphism of the function field attached to $\gamma^{-1}$ carries the $C_0$-twisted coordinates of the $v$-th torsion point of the Tate curve to those of the $v\sigma$-th point, up to the weight-one cocycle unit $\mu$. It is used by [`ModularCurve.FullLevel.zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_of_exists_ringHom`](thm.html#ModularCurve.FullLevel.zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_of_exists_ringHom), where additivity of the transported points at the cusp is deduced.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_AuxLevel_levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.FullLevel.AuxLevel.levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓ)))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M')))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L (q * ℓ) ξ (q * ℓ) ((q * ℓ) ^ 2 * M')
      (ModularCurve.FullLevel.levelH (q * ℓ) M') γ⁻¹ K τ)

    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hC₀ : haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)))

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).2 + (ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![1, 0]).1) * (2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)), -((γ 1 0 : ℤ) : ZMod (q * ℓ))]).1 + HahnSeries.C ((12 : L)⁻¹))))
    (v : Fin 2 → ZMod (q * ℓ)) (hv : v ≠ 0)
    (X Y X' Y' : ↥K)
    (hX : ((X : ↥K) : LaurentSeries L) = ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v).1 - C₀.r))
    (hY : ((Y : ↥K) : LaurentSeries L) = ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 3 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v).2 - C₀.s * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v).1 - C₀.r) - C₀.t))
    (hX' : ((X' : ↥K) : LaurentSeries L) =
      ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)) * v 0 - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * v 1, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * v 0) + ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * v 1]).1 - C₀.r))
    (hY' : ((Y' : ↥K) : LaurentSeries L) =
      ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 3 * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)) * v 0 - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * v 1, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * v 0) + ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * v 1]).2 - C₀.s * ((ModularCurve.cuspPoint L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit ![((γ 0 0 : ℤ) : ZMod (q * ℓ)) * v 0 - ((γ 0 1 : ℤ) : ZMod (q * ℓ)) * v 1, -(((γ 1 0 : ℤ) : ZMod (q * ℓ)) * v 0) + ((γ 1 1 : ℤ) : ZMod (q * ℓ)) * v 1]).1 - C₀.r) - C₀.t)) :
    τ X = ((μ : (↥K)ˣ) : ↥K) ^ 2 * X' ∧ τ Y = ((μ : (↥K)ˣ) : ↥K) ^ 3 * Y' := by sorry
