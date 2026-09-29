-- Prove2me | Theorems.Thm_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar
-- name    : ModularCurve.algebraMap_coeff_zero_sub_not_isUnit_bar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/68e2ddab-5998-535d-bf9e-c5e3197c50b7
-- title:
--   Constant term minus f is a non-unit at ∞
-- statement:
--   Let $L$ be a field and let $F$ be an intermediate field of the extension $L \subseteq L((q))$ of $L$ by the field of Laurent series over $L$; for $f \in F$ write `qSeriesBar L F f` for $f$ regarded as a Laurent series over $L$. Assume $h$: there exists $j \in F$ whose associated Laurent series has order exactly $-1$. Under this hypothesis `qInftyPlaceBar L F h` is the place of $F$ over $L$ whose valuation subring is `qIntegersBar L F`, the set of $f \in F$ whose Laurent series has non-negative order (a valuation subring containing the image of $L$, proper, and a principal ideal ring, the last two facts using $h$). Let $f$ be an element of this valuation subring $\mathcal{O}$, and let $c$ be the coefficient of $q^{0}$ in the Laurent series of $f$. The assertion is that the element $\mathrm{algebraMap}_{L \to \mathcal{O}}(c) - f$ of $\mathcal{O}$ is not a unit of $\mathcal{O}$; equivalently, $f$ is congruent to its constant coefficient modulo the maximal ideal of $\mathcal{O}$.
--
--   This is the computation of the residue map at the cusp $\infty$ on $q$-integral elements of $F$: the residue of $f$ is its constant $q$-coefficient. It is used to evaluate elements at `qInftyPlaceBar` and to prove that $L$ surjects onto the residue field of that place, via [`ModularCurve.evalAt_qInftyPlaceBar_eq_coeff_zero`](thm.html#ModularCurve.evalAt_qInftyPlaceBar_eq_coeff_zero) and [`ModularCurve.surjective_algebraMap_residueField_bar`](thm.html#ModularCurve.surjective_algebraMap_residueField_bar).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_algebraMap_coeff_zero_sub_not_isUnit_bar.lean

import Definitions.Def_ModularCurve_QAdicPlace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.algebraMap_coeff_zero_sub_not_isUnit_bar (L : Type*) [Field L] {F : IntermediateField L (LaurentSeries L)} (h : ∃ j : F, (qSeriesBar L F j).order = -1) (f : (qInftyPlaceBar L F h).toValuationSubring) : ¬IsUnit (algebraMap L (qInftyPlaceBar L F h).toValuationSubring ((qSeriesBar L F (f : F)).coeff 0) - f) := by sorry
