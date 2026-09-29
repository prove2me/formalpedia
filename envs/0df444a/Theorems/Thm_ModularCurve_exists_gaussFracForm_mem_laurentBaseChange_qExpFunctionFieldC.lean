-- Prove2me | Theorems.Thm_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
-- name    : ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/515935c6-3256-5c90-a134-8e1c7ff5bb78
-- title:
--   Gauss fraction form inside the q-expansion function field
-- statement:
--   Let $L$ be a field of characteristic zero (an algebra over $\mathbb{Q}$), let $A$ be a valuation subring of $L$, and let $\Gamma$ be a subgroup of $\mathrm{SL}_2(\mathbb{Z})$ containing the translation matrix `ModularGroup.T`. Write $F_0 =$ `qExpFunctionFieldC ℚ Γ` for the intermediate field of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the set `intFormRatiosC ℚ Γ` of quotients `intSeriesC ℚ pf / intSeriesC ℚ pg`, taken over integers $k$, modular forms $f,g$ of weight $k$ for the image of $\Gamma$ in $\mathrm{GL}_2(\mathbb{R})$ and integral power series $pf,pg$ with `IsIntegralQExp f pf`, `IsIntegralQExp g pg` and `intSeriesC ℚ pg ≠ 0`; and write $F =$ `laurentBaseChange L F₀` for the intermediate field of $L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise embedding `coeffMap (algebraMap ℚ L)`. Then for every nonzero $f \in F$ there are a scalar $c \in L$ and Laurent series $x,y$ with coefficients in $A$ such that $c \neq 0$, the coefficientwise reductions of $x$ and of $y$ along the residue map of $A$ are both nonzero, the coefficientwise images `coeffMap A.subtype x` and `coeffMap A.subtype y` both lie in $F$, and, as elements of $L((q))$, $f \cdot \iota(y) = c \cdot \iota(x)$, where $\iota =$ `coeffMap A.subtype` denotes the coefficientwise inclusion $A((q)) \to L((q))$.
--
--   This is the Gauss-type normal form for elements of the $q$-expansion function field at level $\Gamma$ after base change to $L$: every nonzero element is a scalar multiple of a quotient of two $A$-integral Laurent series which are primitive (nonzero reduction) and which themselves belong to the function field. It is used in the study of automorphisms and reductions of modular curves at full level, where it feeds into the comparison of level automorphisms with the action on the cusps, as in [`ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq`](thm.html#ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq) and its variants; the single ingredient it cites is [`ModularCurve.exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC`](thm.html#ModularCurve.exists_mem_qExpFunctionFieldC_single_mul_intSeriesC_mul_eq_of_mem_intFormRatiosC), which puts the generating ratios in such a form.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC.lean

import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.exists_gaussFracForm_mem_laurentBaseChange_qExpFunctionFieldC
    (L : Type*) [Field L] [Algebra ℚ L] (A : ValuationSubring L)
    (Γ : Subgroup SL(2, ℤ)) (hT : ModularGroup.T ∈ Γ)
    (f : ↥(laurentBaseChange L (qExpFunctionFieldC ℚ Γ))) (hf : f ≠ 0) :
    ∃ (c : L) (x y : LaurentSeries ↥A), c ≠ 0 ∧
      coeffMap (IsLocalRing.residue ↥A) x ≠ 0 ∧ coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
      coeffMap A.subtype x ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ∧
      coeffMap A.subtype y ∈ laurentBaseChange L (qExpFunctionFieldC ℚ Γ) ∧
      (f : LaurentSeries L) * coeffMap A.subtype y = algebraMap L (LaurentSeries L) c * coeffMap A.subtype x := by sorry
