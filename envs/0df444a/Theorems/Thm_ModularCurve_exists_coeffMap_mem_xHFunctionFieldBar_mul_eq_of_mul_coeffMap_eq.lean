-- Prove2me | Theorems.Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
-- name    : ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/f85314f8-b633-5619-abac-0125f8d7498d
-- title:
--   Gauss-integral witnesses may be taken modular on X_H(M)
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \leq (\mathbb{Z}/M\mathbb{Z})^\times$, and assume $p \mid M$ but $p^2 \nmid M$ (so $p$ exactly divides $M$). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$, viewed in $\overline{\mathbb{Q}}$, belongs to the non-units of $A$; write $\kappa$ for the residue field of $A$. Let $F_M = \mathtt{xHFunctionFieldBar}\,M\,H$ be the intermediate field of $\overline{\mathbb{Q}} \subseteq \overline{\mathbb{Q}}((q))$ obtained by base change along $\overline{\mathbb{Q}}$ from the function field $\mathtt{xHFunctionField}\,M\,H$ of $X_H(M)$, realised inside Laurent series by $q$-expansion, and let $f \in F_M$. Suppose $x, y$ are Laurent series with coefficients in $A$ such that the coefficientwise reduction of $y$ to $\kappa((q))$ is non-zero and such that $f \cdot y = x$ holds after pushing $x$ and $y$ forward coefficientwise along $A \hookrightarrow \overline{\mathbb{Q}}$. Then there exist Laurent series $x', y'$ with coefficients in $A$ whose coefficientwise images in $\overline{\mathbb{Q}}((q))$ both lie in $F_M$, such that the reduction of $y'$ to $\kappa((q))$ is non-zero and $f \cdot y' = x'$ in $\overline{\mathbb{Q}}((q))$.
--
--   This is the statement that an element of the function field of $X_H(M)$ which is Gauss-integral at a place $A$ of $\overline{\mathbb{Q}}$ above $p$ — a quotient of Laurent series with $A$-integral coefficients whose denominator has non-zero reduction — can be written as such a quotient with both numerator and denominator themselves $q$-expansions of functions on $X_H(M)$ with $A$-integral coefficients, the denominator being primitive. It is used in the study of specialisation of places of the function field of $X_H(M)$ at $p$ and of the model of $X_H$ at $p$, for instance in the characterisation of the Gauss-integral elements of a place's valuation ring and in the comparison of residues of $q$-expansions with their Frobenius twists.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq.lean

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

theorem ModularCurve.exists_coeffMap_mem_xHFunctionFieldBar_mul_eq_of_mul_coeffMap_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (f : ↥(xHFunctionFieldBar M H)) (x y : LaurentSeries ↥A) (hy : coeffMap (IsLocalRing.residue ↥A) y ≠ 0)
    (hxy : ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) :
    ∃ x' y' : LaurentSeries ↥A,
      coeffMap A.subtype x' ∈ xHFunctionFieldBar M H ∧ coeffMap A.subtype y' ∈ xHFunctionFieldBar M H ∧
      coeffMap (IsLocalRing.residue ↥A) y' ≠ 0 ∧
      ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y' = coeffMap A.subtype x' := by sorry
