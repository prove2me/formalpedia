-- Prove2me | Theorems.Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq_all
-- name    : ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq_all
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/f6b307e4-9842-5d12-919f-da7fd533f80d
-- title:
--   Function-field witnesses for integral quotients in ℚ̄((q))
-- statement:
--   Fix a prime $p$, an integer $N \neq 0$ and a subgroup $H \le (\mathbb{Z}/N)^{\times}$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of `LiesOverPrime`, i.e. the image of $p$ in $\overline{\mathbb{Q}}$ is a non-unit of $A$. Let $f$ be an element of `xHFunctionFieldBar N H`, the intermediate field $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ obtained from `xHFunctionField N H` by base change along `laurentBaseChange`. Suppose given Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ along the residue map $A \to A/\mathfrak{m}_A$ is non-zero, and such that, after applying the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ coefficientwise, $f \cdot y = x$ in $\overline{\mathbb{Q}}((q))$. The conclusion is that such a presentation of $f$ may be arranged inside the function field: there are Laurent series $x', y'$ with coefficients in $A$ whose coefficientwise images in $\overline{\mathbb{Q}}((q))$ both lie in `xHFunctionFieldBar N H`, such that the reduction of $y'$ modulo $\mathfrak{m}_A$ is non-zero and $f \cdot y' = x'$ in $\overline{\mathbb{Q}}((q))$.
--
--   This is the statement that an element of the $\overline{\mathbb{Q}}$-function field of $X_H(N)$ which is a quotient of two $A$-integral $q$-expansions with non-vanishing reduction of the denominator is already such a quotient with both numerator and denominator the $q$-expansions of functions of level $\Gamma_H(N)$; it is the form of the statement with no divisibility relation imposed between $p$ and $N$. It is used in the construction of prolongation data for specialisation of places on $J_H$, and by the variant of the same statement formulated at a level divisible by $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq_all.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq_all
    (p N : ℕ) [Fact p.Prime] [NeZero N] (H : Subgroup (ZMod N)ˣ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (f : ↥(xHFunctionFieldBar N H)) (x y : LaurentSeries ↥A) (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (hxy : ((f : ↥(xHFunctionFieldBar N H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ x' y' : LaurentSeries ↥A,
      coeffMap A.subtype x' ∈ xHFunctionFieldBar N H ∧ coeffMap A.subtype y' ∈ xHFunctionFieldBar N H ∧
      coeffMap (IsLocalRing.residue ↥A) y' ≠ 0 ∧
      ((f : ↥(xHFunctionFieldBar N H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y' = coeffMap A.subtype x' := by sorry
