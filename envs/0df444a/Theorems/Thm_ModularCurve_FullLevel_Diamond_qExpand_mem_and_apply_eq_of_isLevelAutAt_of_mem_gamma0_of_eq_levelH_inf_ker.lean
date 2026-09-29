-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_Diamond_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
-- name    : ModularCurve.FullLevel.Diamond.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:30.533368+00:00
-- url     : https://prove2.me/theorems/8c79b54b-1d18-5a44-837e-d9cb0f4df651
-- title:
--   Stretched Γ₀(M') expansions lie in K and are level-fixed
-- statement:
--   Fix a prime $q$ and $M'\ge 1$ with $q\nmid M'$, and a prime $\ell_g$ with $\ell_g\equiv 11\pmod{12}$ and $\ell_g\mid M'$. Let $L$ be a field of characteristic $0$, $\zeta\in L$ a primitive $q$-th root of unity, and assume there is a ring homomorphism $\iota\colon L\to\mathbb C$ with $\iota(\zeta)=e^{2\pi i/q}$. Let $H_1\le(\mathbb Z/q^2M')^\times$ be the intersection of `levelH q M'`, the kernel of reduction along $q\mid q^2M'$, with the kernel of reduction along $\ell_g\mid q^2M'$, and let $K$ be the intermediate field of $\mathrm{LaurentSeries}(L)$ generated over $L$ by the coefficientwise image under $\mathbb Q\to L$ of `xHFunctionField (q^2*M') H₁`. Then for every Laurent series $x$ over $L$ lying in the subfield generated over $L$ by the coefficientwise images of the field `qExpFunctionFieldC ℚ (Gamma0 M')` — the field generated over $\mathbb Q$ by the ratios $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ of integral $q$-expansions of weight-$k$ forms on $\Gamma_0(M')$ — the series $\mathrm{qExpand}_L^q(x)$, obtained by the exponent-stretching substitution $\mathsf q\mapsto\mathsf q^{\,q}$, lies in $K$, and for every $w\in K$ whose underlying series is $\mathrm{qExpand}_L^q(x)$, every $\gamma\in\Gamma_0(M')$ and every $L$-algebra automorphism $\tau$ of $K$ satisfying `IsLevelAutAt L q ζ q (q^2*M') H₁ γ⁻¹ K τ` one has $\tau(w)=w$. Here the latter condition says: whenever $x_0\in K$ has underlying series the image of $\mathrm{intSeriesC}\,p_f/\mathrm{intSeriesC}\,p_g$ for weight-$k$ forms $f,g$ on $\Gamma_{H_1}(q^2M')$ with integral $q$-expansions $p_f,p_g$ and $\mathrm{intSeriesC}\,p_g\neq 0$, then for every $\iota$ as above the $\iota$-image of $\tau(x_0)$ times the $q$-expansion of $g\mid_k \mathrm{diag}(q,1)^{-1}\gamma^{-1}\mathrm{diag}(q,1)$ equals that of $f\mid_k\mathrm{diag}(q,1)^{-1}\gamma^{-1}\mathrm{diag}(q,1)$.
--
--   Classically this is the statement that the stretched function $F(qz)$, for $F$ a modular function on $\Gamma_0(M')$, is a function on the $H_1$ level structure of level $q^2M'$ and is fixed by the level automorphism attached to $\gamma^{-1}$ for $\gamma\in\Gamma_0(M')$, since $F(q\cdot\gamma^\sharp z)=F(\gamma(qz))=F(qz)$ with $\gamma^\sharp=\mathrm{diag}(q,1)^{-1}\gamma\,\mathrm{diag}(q,1)$; it supplies the invariance half of the characterisation of the fixed field of the level automorphisms. It is used by the auxiliary diamond-operator computations identifying invariants of chart rings in the integral two-chart model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_Diamond_qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_CoordRing
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory AlgebraicGeometry IsLocalRing AlgebraicCurve.TwoChartIntegralModel

open scoped MatrixGroups

theorem ModularCurve.FullLevel.Diamond.qExpand_mem_and_apply_eq_of_isLevelAutAt_of_mem_gamma0_of_eq_levelH_inf_ker
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓg : ℕ) (hℓg : ℓg.Prime) (hℓg12 : ℓg % 12 = 11) (hℓgM' : ℓg ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    (H₁ : Subgroup (ZMod (q ^ 2 * M'))ˣ)
    (hH₁ : H₁ = ModularCurve.FullLevel.levelH q M' ⊓ (ZMod.unitsMap (Dvd.dvd.mul_left hℓgM' (q ^ 2))).ker)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') H₁)) :
    ∀ x : LaurentSeries L,
      x ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) →
      ModularCurve.qExpand L q x ∈ K ∧
      ∀ w : ↥K, ((w : ↥K) : LaurentSeries L) = ModularCurve.qExpand L q x →
        ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
          ∀ τ : ↥K ≃ₐ[L] ↥K, ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') H₁ γ⁻¹ K τ →
            τ w = w := by sorry
