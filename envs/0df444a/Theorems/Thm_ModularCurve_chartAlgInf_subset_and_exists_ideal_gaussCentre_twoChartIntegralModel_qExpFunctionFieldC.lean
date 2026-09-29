-- Prove2me | Theorems.Thm_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
-- name    : ModularCurve.chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/b3dbadab-f2d8-52b3-8287-d76b2ecb0ae0
-- title:
--   Gauss point lies on the pole chart of the integral model
-- statement:
--   Let $\Gamma\le \mathrm{SL}(2,\mathbb{Z})$ be a subgroup of finite index containing the translation matrix $T$, let $p$ be a prime, and let $F=$ `qExpFunctionFieldC ℚ Γ` be the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the ratios $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ attached to integral $q$-expansions $p_f,p_g\in\mathbb{Z}[[q]]$ of modular forms $f,g$ of one and the same weight on $\Gamma$ (with $\mathrm{intSeriesC}(p_g)\ne 0$). Let $j\in F$ be a nonzero element whose underlying Laurent series is `jqModC ℚ`, that is $q^{-1}$ times the image in $\mathbb{Q}[[q]]$ of $\mathrm{jNum}=E_4^{3}\cdot(\text{inverse Dedekind }\eta\text{ unit})$. Write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of $\mathbb{Q}$ of rationals whose denominator is coprime to $p$. Let $W_0$ be a valuation subring of $F$ whose elements are exactly the $f$ for which there are $a,a'\in R[[q]]$ with $a'$ nonzero modulo $p$ (its image under [`GaloisRep.ratLocalizedAtResidue p`](def/GaloisRep_RatLocalizedAtResidue.html#L15) into $(\mathbb{Z}/p)[[q]]$ is nonzero) and $f\cdot a'=a$ in $\mathbb{Q}((q))$. Let $O=$ `TwoChartIntegralModel.chartAlgInf R F j` be the $R$-subalgebra of $F$ of elements integral over $R[j^{-1}]$. Then: first, $O\subseteq W_0$; secondly, there is an ideal $\mathfrak q$ of $O$ consisting exactly of those $b$ whose image in $F$ is a non-unit of $W_0$, such that $\mathfrak q$ is prime, contains $p$, is a minimal prime of the ideal $(p)$ of $O$, every $b\in\mathfrak q$ has $0$-th $q$-coefficient of the form $p\,r$ with $r\in R$, the element $j^{-1}$ of $O$ (namely `TwoChartIntegralModel.jInvChartInf`) does not lie in $\mathfrak q$, and the $0$-th $q$-coefficient of $j^{-1}$ is $0$.
--
--   This is a valuation-theoretic form of the $q$-expansion principle at the cusp $\infty$: the Gauss valuation of the $q$-expansion field at $p$ (sup-norm on coefficients) is centred on the pole chart of the two-chart integral model, at a prime minimal over $p$ that is strictly contained in the ideal of elements with constant term divisible by $p$, so that it corresponds to the generic point of the component of the special fibre through the reduced cusp. It is used in the analysis of the minimal primes of the pole chart and of the germ of the function field at the cusp in the construction of the integral model at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_GaloisRep_RatLocalizedAtResidue

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open AlgebraicCurve ModularCurve

theorem ModularCurve.chartAlgInf_subset_and_exists_ideal_gaussCentre_twoChartIntegralModel_qExpFunctionFieldC
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) :
    (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀) ∧
    ∃ 𝔮 : Ideal ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
      (∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
        b ∈ 𝔮 ↔ (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀.nonunits) ∧
      𝔮.IsPrime ∧
      ((p : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j)) ∈ 𝔮) ∧
      𝔮 ∈ (Ideal.span {(p : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))}).minimalPrimes ∧
      (∀ b ∈ 𝔮, ∃ r : ℚ, r ∈ GaloisRep.ratLocalizedAt p ∧
        (((b : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)).coeff 0 = (p : ℚ) * r) ∧
      TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j ∉ 𝔮 ∧
      (((TwoChartIntegralModel.jInvChartInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j :
          ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ)).coeff 0 = 0 := by sorry
