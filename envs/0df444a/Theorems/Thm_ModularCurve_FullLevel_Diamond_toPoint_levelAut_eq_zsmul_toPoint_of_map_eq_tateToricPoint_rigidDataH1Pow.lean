-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow
-- name    : ModularCurve.FullLevel.Diamond.toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/afe3a7aa-eee1-53a5-95ff-40e7134b6d06
-- title:
--   Diamond action on the toric point of the Tate curve
-- statement:
--   Fix a prime $q$ and $M'\ge 1$ with $q\nmid M'$, and a prime $\ell_g$ with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic zero, $\xi\in L$ a primitive $(q\ell_g)$-th root of unity admitting a ring map $\iota_0:L\to\mathbb C$ with $\iota_0(\xi)=e^{2\pi i/(q\ell_g)}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of the kernel of reduction to $(\mathbb Z/q)^\times$ with the kernel of reduction to $(\mathbb Z/\ell_g)^\times$, and let $K\subseteq L(\!(\mathsf q)\!)$ be the subfield generated over $L$ by the coefficientwise image of the function field of $X_{H_1}(q^2M')$ (a decidable equality on $K$ is assumed). Let $\gamma\in\mathrm{SL}_2(\mathbb Z)$ lie in $\Gamma_0(M')$ and let $\tau$ be an $L$-algebra automorphism of $K$ satisfying `IsLevelAutAt` for $q$, $\xi^{\ell_g}$, $q$, level $(q^2M',H_1)$ and $\gamma^{-1}$: for all weights $k$, all modular forms $f,g$ for $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions, $g$ having nonzero associated series, and all $x\in K$ whose Laurent expansion is the coefficient embedding of the ratio of those series, the $\iota$-image of $\tau x$ times the $q$-expansion of $g\mid_k(\mathrm{diag}(q,1)^{-1}\gamma^{-1}\mathrm{diag}(q,1))$ equals that of $f$ likewise translated, for every $\iota:L\to\mathbb C$ with $\iota(\xi^{\ell_g})=e^{2\pi i/q}$. Write $P_c=(x_c,y_c)$ for `tateToricPoint L q c`, the explicit pair of Laurent series attached to a unit $c$, and let $c_0=\xi^q$ viewed as a unit of $L$. The Weierstrass variable change $C_0$ over $L(\!(\mathsf q)\!)$ is required to satisfy $u_{C_0}\,(2x_{c_0}+\tfrac16)=2y_{c_0}+x_{c_0}$, $r=-\tfrac1{12}$, $s=-\tfrac12$, $t=\tfrac1{24}$ (constant Hahn series), and $\mu\in K^\times$ is required to satisfy $\mu\,(2y_{c_0^{\gamma_{00}}}+x_{c_0^{\gamma_{00}}})\cdot 2(x_{c_0}+\tfrac1{12}) = (2y_{c_0}+x_{c_0})\cdot 2(x_{c_0^{\gamma_{00}}}+\tfrac1{12})$, where $\gamma_{00}$ is the upper-left entry of $\gamma$ read in $\mathbb Z$. Finally $W$ is a Weierstrass curve over $K$ whose base change to $L(\!(\mathsf q)\!)$ is $C_0\cdot\mathrm{Tate}$ (the Tate base curve for $q$), and $D$ is a level-$P$ datum $(x_P,y_P,x_Q,y_Q)$ over $K$ whose base change is the $C_0$-transport of the datum $(x_{c_0},y_{c_0},x_{c_0},y_{c_0})$. The conclusion is that $(\mu^{-2}\tau(x_P),\ \mu^{-3}\tau(y_P))$ is a nonsingular point of the affine model of $W$, and that the associated point of $W$ (the point with these coordinates if nonsingular, and $0$ otherwise) equals $\gamma_{00}$ times the point associated to $(x_P,y_P)$ in the group $W(K)$.
--
--   This is the $\Gamma_1(\ell_g)$-slot analogue of the corresponding statement for the cusp pair: it says that the level automorphism $\tau$, corrected by the unit $\mu$ coming from the weight-one comparison, acts on the transported toric point of the Tate curve as the diamond operator $P\mapsto[\gamma_{00}]P$. It is the input to [`ModularCurve.FullLevel.Diamond.toPoint_level_snd_fst_act_mapRing_eq_zsmul_toPoint_of_curve_eq_units_rigidDataH1Pow`](thm.html#ModularCurve.FullLevel.Diamond.toPoint_level_snd_fst_act_mapRing_eq_zsmul_toPoint_of_curve_eq_units_rigidDataH1Pow), where the diamond action on the moduli-theoretic slot at level $H_1$ is identified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow.lean

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

theorem ModularCurve.FullLevel.Diamond.toPoint_levelAut_eq_zsmul_toPoint_of_map_eq_tateToricPoint_rigidDataH1Pow
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
    [DecidableEq ↥K]
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
    (D : ModularCurve.LevelPData ↥K)
    (hD : haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
      D.map (algebraMap ↥K (LaurentSeries L)) =
        ((⟨(ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1, (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2, (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).1, (ModularCurve.tateToricPoint L q ((hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero hℓg.ne_zero)).unit ^ q)).2⟩ :
            ModularCurve.LevelPData (LaurentSeries L)).variableChange C₀)) :
    W.toAffine.Nonsingular (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP) ∧
    ModularCurve.LevelRelabelling.toPoint W (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 2 * τ D.xP) (((μ⁻¹ : (↥K)ˣ) : ↥K) ^ 3 * τ D.yP) =
      (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0) • ModularCurve.LevelRelabelling.toPoint W D.xP D.yP := by sorry
