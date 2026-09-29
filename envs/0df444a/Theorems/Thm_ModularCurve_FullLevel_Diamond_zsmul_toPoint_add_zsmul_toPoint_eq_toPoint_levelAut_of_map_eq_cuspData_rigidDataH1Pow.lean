-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/bfec689b-1e2a-506c-9a8d-ed32ed879b6d
-- title:
--   Level automorphism relabels the Tate cusp pair by γ
-- statement:
--   Fix a prime $q$, an integer $M'\ge 1$ with $q\nmid M'$, and a prime $\ell_g$ with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell_g)$-th root of unity admitting a ring homomorphism $\iota_0:L\to\mathbb C$ with $\iota_0(\xi)=e^{2\pi i/(q\ell_g)}$, and let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernels of reduction to $(\mathbb Z/q)^\times$ and to $(\mathbb Z/\ell_g)^\times$. Let $K\subseteq L((\mathsf q))$ be the intermediate field generated over $L$ by the image, under the coefficient embedding of $\mathbb Q((\mathsf q))$ in $L((\mathsf q))$, of the function field of $X_{H_1}(q^2M')$. Let $\gamma\in\Gamma_0(M')\subseteq \mathrm{SL}_2(\mathbb Z)$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for the data $(L,q,\xi^{\ell_g},q,q^2M',H_1,\gamma^{-1},K)$: for all weights $k$, all modular forms $f,g$ on $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f,p_g$, $p_g\neq0$, all $x\in K$ whose Laurent expansion is the coefficient embedding of $p_f/p_g$, and all $\iota:L\to\mathbb C$ with $\iota(\xi^{\ell_g})=e^{2\pi i/q}$, one has $\iota(\tau x)\cdot \hat q(g\mid_k \gamma^{-\sharp})=\hat q(f\mid_k\gamma^{-\sharp})$, where $\sharp$ denotes conjugation by $\mathrm{diag}(q,1)$ as encoded by `conjElemN`. Write $P_c$ for `tateToricPoint L q c`, the pair of Laurent series attached to a unit $c$, and put $\zeta=\xi^{q}$ viewed as a unit of $L$, $a=\gamma_{00}$. Let $C_0$ be a Weierstrass variable change over $L((\mathsf q))$ with $r=-1/12$, $s=-1/2$, $t=1/24$ and with its unit $u$ normalised by $u\,(2X(P_\zeta)+1/6)=2Y(P_\zeta)+X(P_\zeta)$, and let $\mu\in K^\times$ satisfy the cocycle identity $\mu\,(2Y(P_{\zeta^a})+X(P_{\zeta^a}))\cdot 2(X(P_\zeta)+1/12)=(2Y(P_\zeta)+X(P_\zeta))\cdot 2(X(P_{\zeta^a})+1/12)$ in $L((\mathsf q))$. Let $W$ be a Weierstrass curve over $K$ whose base change to $L((\mathsf q))$ is $C_0\cdot\mathrm{Tate}(\mathsf q^{\,q})$, i.e. $C_0$ applied to `tateBase L q`, and let $n\in\mathbb Z/q$ be nonzero. Let $D$ be a quadruple $(x_P,y_P,x_Q,y_Q)$ of elements of $K$ whose base change to $L((\mathsf q))$ is the $C_0$-transform of the cusp data `cuspData L q` at $\xi^{\ell_g}$ for the vectors $(n,0)$ and $(0,-n)$. Then the pairs $(\mu^{-2}\tau x_P,\mu^{-3}\tau y_P)$ and $(\mu^{-2}\tau x_Q,\mu^{-3}\tau y_Q)$ are nonsingular points of the affine model of $W$, and, writing $\mathrm{toPoint}(x,y)$ for the point $(x,y)$ when it is nonsingular and $0$ otherwise, $$\gamma_{00}\,\mathrm{toPoint}(x_P,y_P)+\gamma_{10}\,\mathrm{toPoint}(x_Q,y_Q)=\mathrm{toPoint}(\mu^{-2}\tau x_P,\mu^{-3}\tau y_P),$$ $$\gamma_{01}\,\mathrm{toPoint}(x_P,y_P)+\gamma_{11}\,\mathrm{toPoint}(x_Q,y_Q)=\mathrm{toPoint}(\mu^{-2}\tau x_Q,\mu^{-3}\tau y_Q),$$ the integer multiples being taken in the group of points of the affine model of $W$.
--
--   This is the cusp-by-cusp Galois equivariance computation for full level-$q$ structures in the $H_1$-frame: the automorphism $\tau$ of the function field, after the weight-one twist by $\mu$, permutes the pair of $q$-division points read at the cusp exactly as the matrix $\gamma$ relabels a basis. It is used in the construction of the diamond-operator action on the level datum, in [`ModularCurve.FullLevel.Diamond.exists_level_snd_snd_act_mapRing_eq_relabel_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.exists_level_snd_snd_act_mapRing_eq_relabel_rigidDataH1Pow).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow.lean

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.zsmul_toPoint_add_zsmul_toPoint_eq_toPoint_levelAut_of_map_eq_cuspData_rigidDataH1Pow
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓg))
    (hιξ : ∃ ι : L →+* ℂ, ι ξ = Complex.exp (2 * Real.pi * Complex.I / (q * ℓg)))
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

    (W : WeierstrassCurve ↥K)
    (hW : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      W.map (algebraMap ↥K (LaurentSeries L)) = C₀ • ModularCurve.tateBase L q)
    (n : ZMod q) (hn : n ≠ 0)
    (D : ModularCurve.LevelPData ↥K)
    (hD : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      D.map (algebraMap ↥K (LaurentSeries L)) =
      (ModularCurve.cuspData L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ ℓg) ![(n : ZMod q), 0] ![0, -(n : ZMod q)]).variableChange C₀) :

    haveI : DecidableEq ↥K := fun a b => Classical.propDecidable (a = b)
    (W.toAffine.Nonsingular (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP) ∧
      W.toAffine.Nonsingular (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xQ) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yQ)) ∧
    (γ 0 0 : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + (γ 1 0 : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ =
      ModularCurve.LevelRelabelling.toPoint W (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP) ∧
    (γ 0 1 : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP + (γ 1 1 : ℤ) • ModularCurve.LevelRelabelling.toPoint W D.xQ D.yQ =
      ModularCurve.LevelRelabelling.toPoint W (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xQ) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yQ) := by sorry
