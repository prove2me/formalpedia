-- Prove2me | Theorems.Thm_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
-- name    : ModularCurve.mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/03dc5e95-5ba1-5b32-acab-b9fb8cd05f6d
-- title:
--   Gauss valuation ring as a localisation of the pole chart
-- statement:
--   Let $\Gamma\le\mathrm{SL}_2(\mathbb{Z})$ be a subgroup of finite index containing the translation matrix $T$, let $p$ be a prime, and let $F=$ `qExpFunctionFieldC ℚ Γ` be the subfield of $\mathbb{Q}((q))$ obtained by adjoining to $\mathbb{Q}$ all quotients $\mathrm{intSeriesC}(p_f)/\mathrm{intSeriesC}(p_g)$ of integral $q$-expansions of modular forms of level $\Gamma$. Let $j\in F$ be nonzero with Laurent expansion `jqModC ℚ`, namely $q^{-1}$ times the integral series $E_4^3\cdot\eta^{-24}$-type numerator `jNum` pushed to $\mathbb{Q}$. Write $R=$ [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) for the subring of rationals with denominator coprime to $p$, and let $O=$ `chartAlgInf` be the integral closure of $R[j^{-1}]$ in $F$. Assume $W_0$ is a valuation subring of $F$ whose elements are exactly those $f$ for which there are power series $a,a'$ over $R$ with the reduction of $a'$ along [`GaloisRep.ratLocalizedAtResidue p`](def/GaloisRep_RatLocalizedAtResidue.html#L15) nonzero in $(\mathbb{Z}/p)[[q]]$ and $f\cdot a'=a$ in $\mathbb{Q}((q))$; and that $\mathfrak q$ is the ideal of $O$ consisting of those $b$ whose image in $F$ is a nonunit of $W_0$. Then for every $f\in F$: $f\in W_0$ if and only if $f\cdot b=a$ for some $a,b\in O$ with $b\notin\mathfrak q$.
--
--   This identifies the Gauss valuation ring of $F$ at $p$ — defined by clearing denominators against a $q$-expansion that is not divisible by $p$ — with the local ring $O_{\mathfrak q}$ of the pole chart of the two-chart integral model at the centre of that valuation, the generic point of the component of the special fibre through the cusp $\infty$; it is the valuation-theoretic form of the $q$-expansion principle. It is used in the construction of the mod $p$ reduction data attached to $X_H$ and in the comparison of diamond operators with coefficient embeddings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre.lean

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

theorem ModularCurve.mem_gaussValuationSubring_iff_exists_chartAlgInf_mul_eq_of_not_mem_gaussCentre
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ) (p : ℕ) [Fact p.Prime]
    (j : ↥(qExpFunctionFieldC ℚ Γ)) [Fact (j ≠ 0)] (hj : (j : LaurentSeries ℚ) = jqModC ℚ)
    (W₀ : ValuationSubring ↥(qExpFunctionFieldC ℚ Γ))
    (hW₀ : ∀ f : ↥(qExpFunctionFieldC ℚ Γ), f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype))
    (𝔮 : Ideal ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j))
    (h𝔮 : ∀ b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
      b ∈ 𝔮 ↔ (b : ↥(qExpFunctionFieldC ℚ Γ)) ∈ W₀.nonunits)
    (f : ↥(qExpFunctionFieldC ℚ Γ)) :
    f ∈ W₀ ↔ ∃ a b : ↥(TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ Γ) j),
      b ∉ 𝔮 ∧ f * (b : ↥(qExpFunctionFieldC ℚ Γ)) = (a : ↥(qExpFunctionFieldC ℚ Γ)) := by sorry
