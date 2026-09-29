-- Prove2me | Theorems.Thm_ModularCurve_qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss
-- name    : ModularCurve.qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/a640625c-fb8f-5d21-8a64-9a6458290452
-- title:
--   The cusp coordinate t=j(qᵖ)/jᵖ at the prime p
-- statement:
--   Let $p$ be a prime, and let $K$ be an intermediate field of $\mathbb{Q} \subseteq \mathbb{Q}((q))$ (the field of Laurent series over $\mathbb{Q}$). Let $j \in K$, assumed nonzero, whose Laurent series is `jqModC` $= q^{-1}\cdot \mathrm{jNum}$, the $q$-expansion of the modular invariant, and let $j' \in K$ have Laurent series `qExpand` $\mathbb{Q}\,p$ applied to that series, i.e. the same series with exponents multiplied by $p$ (the expansion in $q^p$). Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $K$ interchanging $j$ and $j'$. Let $W_0$ be a valuation subring of $K$ whose elements are exactly the $f$ for which there are power series $a, a'$ with coefficients in the subring $\mathrm{ratLocalizedAt}\ p \subseteq \mathbb{Q}$ of rationals whose denominator is coprime to $p$ (i.e. $\mathbb{Z}_{(p)}$), with the coefficientwise reduction of $a'$ along $\mathrm{ratLocalizedAtResidue}\ p : \mathbb{Z}_{(p)} \to \mathbb{Z}/p$ nonzero, and $f \cdot a' = a$ as Laurent series over $\mathbb{Q}$. Put $u = j^{-1}$ and $t = j'u^p$. The assertion is: $t$ lies in `chartAlgInf` $\mathbb{Z}_{(p)}\ K\ j$, the subalgebra of elements of $K$ integral over $\mathbb{Z}_{(p)}[j^{-1}]$; the $q^0$-coefficients of $t$ and of $\sigma t$ are $1$ and $0$; moreover $t - 1$ lies in the nonunits of $W_0$ and the $q^0$-coefficient of $\sigma(t-1)$ is $-1$; and $t^p - u^{p^2-1}$ lies in the nonunits of the valuation subring $\sigma^{-1}W_0$ (the comap of $W_0$ along $\sigma$) while its own $q^0$-coefficient is $1$.
--
--   This is the basic analytic input on the cusp coordinate $t = j(q^p)/j(q)^p$ attached to the level-$p$ modular equation: it is integral on the chart at infinity of the two-chart model of $(K,j)$ over $\mathbb{Z}_{(p)}$, takes the values $1$ and $0$ at the two cusps $\infty$ and $\sigma\infty$, and so separates the two branches of the special fibre at $p$. It is used in the study of the integral model of $X_H$ at $p$, notably in the results on the chart at infinity and on the minimal primes of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open Polynomial ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem ModularCurve.qExpand_jq_div_pow_mem_chartAlgInf_and_coeff_zero_and_mem_nonunits_gauss
    (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ (LaurentSeries ℚ))
    (j : ↥K) (hj : (j : LaurentSeries ℚ) = jqModC ℚ) [Fact (j ≠ 0)]
    (j' : ↥K) (hj' : (j' : LaurentSeries ℚ) = qExpand ℚ p (jqModC ℚ))

    (σ : ↥K ≃ₐ[ℚ] ↥K) (hσj : σ j = j') (hσj' : σ j' = j)

    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔
      ∃ a a' : PowerSeries ↥(GaloisRep.ratLocalizedAt p), a'.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 ∧
        (f : LaurentSeries ℚ) * HahnSeries.ofPowerSeries ℤ ℚ (a'.map (GaloisRep.ratLocalizedAt p).subtype) =
          HahnSeries.ofPowerSeries ℤ ℚ (a.map (GaloisRep.ratLocalizedAt p).subtype)) :
    let u : ↥K := j⁻¹
    let t : ↥K := j' * u ^ p

    t ∈ TwoChartIntegralModel.chartAlgInf ↥(GaloisRep.ratLocalizedAt p) ↥K j ∧

    ((t : ↥K) : LaurentSeries ℚ).coeff 0 = 1 ∧
    ((σ t : ↥K) : LaurentSeries ℚ).coeff 0 = 0 ∧

    (t - 1 ∈ W₀.nonunits ∧ ((σ (t - 1) : ↥K) : LaurentSeries ℚ).coeff 0 = -1) ∧
    (t ^ p - u ^ (p ^ 2 - 1) ∈ (W₀.comap σ.toAlgHom.toRingHom).nonunits ∧
      ((t ^ p - u ^ (p ^ 2 - 1) : ↥K) : LaurentSeries ℚ).coeff 0 = 1) := by sorry
