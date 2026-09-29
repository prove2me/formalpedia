-- Prove2me | Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp
-- name    : ModularCurve.ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/33872f77-73a2-5853-9687-d80f4d9a5422
-- title:
--   Order zero of the units Δ(q)/Δ(q^δ) outside the cusps
-- statement:
--   Fix a non-zero natural number $N$ and a non-zero divisor $\delta$ of $N$. Let $\mathrm{modularUnitSeries}\ \delta$ be the Laurent series over $\mathbb{Q}$ given by $\mathrm{deltaSeries} \cdot (\mathrm{qExpand}\ \mathbb{Q}\ \delta\ \mathrm{deltaSeries})^{-1}$, where $\mathrm{deltaSeries} = q \cdot \mathrm{dedekindEtaUnitQ}$ is the $q$-expansion of the discriminant and $\mathrm{qExpand}\ \mathbb{Q}\ \delta$ is substitution $q \mapsto q^{\delta}$; it is assumed to lie in $\mathrm{modularFunctionFieldFull}\ N$, the subfield of $\mathrm{LaurentSeries}\ \mathbb{Q}$ generated over $\mathbb{Q}$ by the series $\mathrm{qExpand}\ \mathbb{Q}\ d\ \mathrm{jq}$ for the non-zero divisors $d$ of $N$. Let $\mathrm{modularFunctionFieldBar}\ N$ be the subfield of $\mathrm{LaurentSeries}\ (\mathrm{AlgebraicClosure}\ \mathbb{Q})$ generated over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ by the coefficientwise images $\mathrm{coeffEmb}$ of the elements of $\mathrm{modularFunctionFieldFull}\ N$. Let $v$ be a place of this field over $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, that is, a valuation subring containing the image of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$, different from the whole field and a principal ideal ring, and assume $v$ is not a cusp for $\mathrm{CharPModel.jBar}\ N$, i.e. the coefficientwise image of the $q$-expansion $\mathrm{jq}$ of $j$ does belong to the valuation subring of $v$. Then the order $v.\mathrm{ord}$ of the element of $\mathrm{modularFunctionFieldBar}\ N$ determined by the coefficientwise image of $\mathrm{modularUnitSeries}\ \delta$, that is minus the logarithm of its adic valuation, is $0$.
--
--   This is the statement that the eta-quotient modular units $\Delta(q)/\Delta(q^{\delta})$, $\delta \mid N$, are supported on the cusps of $X_0(N)$: they are units at every place of the geometric function field at which $j$ is integral. It is used in the analysis of divisors and prolongations of places on the modular curve, where divisors of modular units are compared with the cuspidal part of a specialisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp.lean

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_CuspidalClass

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.ord_coeffEmb_modularUnitSeries_eq_zero_of_not_isCusp (N : ℕ) [NeZero N]
    (δ : ℕ) [NeZero δ] (hδ : δ ∣ N) (hmem : modularUnitSeries δ ∈ modularFunctionFieldFull N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hv : ¬ IsCusp (CharPModel.jBar N) v) :
    v.ord (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries δ),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) hmem⟩ : modularFunctionFieldBar N) = 0 := by sorry
