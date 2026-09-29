-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
-- name    : ModularCurve.FullLevel.Diamond.levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/4d0f18b1-9ab8-5b1b-936d-8fceca05865b
-- title:
--   Level automorphism transports level-q cusp coordinates up to μ
-- statement:
--   Let $q$ be prime, $M'\neq 0$ with $q\nmid M'$, and $\ell_g$ a prime with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $q\ell_g$-th root of unity, and $\iota\colon L\to\mathbb{C}$ a ring map with $\iota(\xi)=e^{2\pi i/(q\ell_g)}$. Let $H_1\le(\mathbb{Z}/q^2M')^\times$ be the intersection of [`ModularCurve.FullLevel.levelH q M'`](def/ModularCurve_FullLevelJacobian.html#L22), the kernel of the unit reduction map attached to the divisibility `dvd_sq_mul q M'`, with the kernel of reduction to $(\mathbb{Z}/\ell_g)^\times$, and let $K$ be the intermediate field of $L(\!(\mathsf q)\!)$ generated over $L$ by the coefficientwise image of the $q$-expansion function field of $\Gamma_{H_1}(q^2M')$ inside $\mathbb{Q}(\!(\mathsf q)\!)$. Let $\gamma\in\Gamma_0(M')\subseteq SL(2,\mathbb{Z})$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for $\gamma^{-1}$ with $\zeta_q=\xi^{\ell_g}$ and width $q$: for every weight $k$, every pair $f,g$ of weight-$k$ forms on $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f,p_g$, $p_g\neq 0$, and every $x\in K$ reading the ratio of those series, the coefficientwise image of $\tau x$ times the $q$-expansion of $g\mid_k\gamma^{-1,\sharp}$ equals that of $f\mid_k\gamma^{-1,\sharp}$, where $\gamma^\sharp=\mathrm{diag}(q,1)^{-1}\gamma\,\mathrm{diag}(q,1)$ is `conjElemN q`. Write $\zeta_{\ell_g}=\xi^q$ and $\zeta_q=\xi^{\ell_g}$ as units, and let $(x_0,y_0)$ be the Tate toric point `tateToricPoint L q` at $\zeta_{\ell_g}$ and $(x_1,y_1)$ that at $\zeta_{\ell_g}^{\gamma_{00}}$. Assume the Weierstrass variable change $C_0$ over $L(\!(\mathsf q)\!)$ has $r=-1/12$, $s=-1/2$, $t=1/24$ and $u\,(2x_0+1/6)=2y_0+x_0$, and that $\mu\in K^\times$ satisfies $\mu\,(2y_1+x_1)\cdot 2(x_0+1/12)=(2y_0+x_0)\cdot 2(x_1+1/12)$. Let $v\in(\mathbb{Z}/q)^2$ be nonzero and set $v\sigma=(\gamma_{00}v_0-\gamma_{01}v_1,\,-\gamma_{10}v_0+\gamma_{11}v_1)$. If $X,Y\in K$ read the $C_0$-transported level-$q$ cusp coordinates $u^{-2}(x_v-r)$, $u^{-3}(y_v-s(x_v-r)-t)$ of `cuspPoint L q` at $\zeta_q$ and $v$, and $X',Y'\in K$ read the same expressions at $v\sigma$, then $\tau X=\mu^2X'$ and $\tau Y=\mu^3Y'$.
--
--   This is the coordinate-transport step for the full-level construction: it says that the level automorphism attached to $\gamma^{-1}$ permutes the weight-one normalised coordinates of the level-$q$ cusp points on the Tate curve according to the index action $v\mapsto v\sigma$, up to the weight-one cocycle $\mu$. It feeds the computation of the induced action on the Tate-curve torsion points used in [`ModularCurve.FullLevel.Diamond.zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow), and rests on the two realisations of these coordinates as ratios of modular forms on $\Gamma_{H_1}(q^2M')$ together with the transfer principle for level automorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange.lean

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

theorem ModularCurve.FullLevel.Diamond.levelAut_apply_eq_unit_pow_mul_of_coe_eq_cuspPoint_variableChange
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (ι : L →+* ℂ) (hι : ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁))
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (τ : ↥K ≃ₐ[L] ↥K)
    (hτ : ModularCurve.FullLevel.IsLevelAutAt L q (ξ ^ ℓg) q (q ^ 2 * M') H₁ γ⁻¹ K τ)

    (C₀ : WeierstrassCurve.VariableChange (LaurentSeries L))
    (hC₀ : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      (((C₀.u : (LaurentSeries L)ˣ) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((6 : L)⁻¹)) =
          2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 ∧
        C₀.r = HahnSeries.C (-(12 : L)⁻¹) ∧ C₀.s = HahnSeries.C (-(2 : L)⁻¹) ∧ C₀.t = HahnSeries.C ((24 : L)⁻¹)))

    (μ : (↥K)ˣ)
    (hμ : (((μ : (↥K)ˣ) : ↥K) : LaurentSeries L) * (2 * (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).2 + (ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).1) * (2 * ((ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1 + HahnSeries.C ((12 : L)⁻¹))) =
      (2 * (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2 + (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1) * (2 * ((ModularCurve.tateToricPoint L q (((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q) ^ ((γ 0 0 : ℤ)))).1 + HahnSeries.C ((12 : L)⁻¹))))
    (v : Fin 2 → ZMod q) (hv : v ≠ 0)
    (X Y X' Y' : ↥K)
    (hX : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ((X : ↥K) : LaurentSeries L) = ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 * ((ModularCurve.cuspPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) v).1 - C₀.r))
    (hY : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ((Y : ↥K) : LaurentSeries L) = ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 3 * ((ModularCurve.cuspPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) v).2 - C₀.s * ((ModularCurve.cuspPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) v).1 - C₀.r) - C₀.t))
    (hX' : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ((X' : ↥K) : LaurentSeries L) =
      ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 2 * ((ModularCurve.cuspPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![((γ 0 0 : ℤ) : ZMod q) * v 0 - ((γ 0 1 : ℤ) : ZMod q) * v 1, -(((γ 1 0 : ℤ) : ZMod q) * v 0) + ((γ 1 1 : ℤ) : ZMod q) * v 1]).1 - C₀.r))
    (hY' : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      ((Y' : ↥K) : LaurentSeries L) =
      ((C₀.u⁻¹ : (LaurentSeries L)ˣ) : LaurentSeries L) ^ 3 * ((ModularCurve.cuspPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![((γ 0 0 : ℤ) : ZMod q) * v 0 - ((γ 0 1 : ℤ) : ZMod q) * v 1, -(((γ 1 0 : ℤ) : ZMod q) * v 0) + ((γ 1 1 : ℤ) : ZMod q) * v 1]).2 - C₀.s * ((ModularCurve.cuspPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![((γ 0 0 : ℤ) : ZMod q) * v 0 - ((γ 0 1 : ℤ) : ZMod q) * v 1, -(((γ 1 0 : ℤ) : ZMod q) * v 0) + ((γ 1 1 : ℤ) : ZMod q) * v 1]).1 - C₀.r) - C₀.t)) :
    τ X = ((μ : (↥K)ˣ) : ↥K) ^ 2 * X' ∧ τ Y = ((μ : (↥K)ˣ) : ↥K) ^ 3 * Y' := by sorry
