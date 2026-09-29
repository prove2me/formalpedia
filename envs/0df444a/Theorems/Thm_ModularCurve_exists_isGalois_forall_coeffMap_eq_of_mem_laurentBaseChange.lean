-- Prove2me | Theorems.Thm_ModularCurve_exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange
-- name    : ModularCurve.exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.903374+00:00
-- url     : https://prove2.me/theorems/c6e08ef5-d9a0-5a3d-826a-04af983754df
-- title:
--   Finitely many Laurent elements defined over one finite Galois extension
-- statement:
--   Let $F_0$ be an intermediate field of $\mathbb{Q}$ in the field $\mathbb{Q}((q))$ of Laurent series over $\mathbb{Q}$, and for a field $L$ containing $\mathbb{Q}$ let $L\cdot F_0$ denote `laurentBaseChange L F₀`, the intermediate field of $L$ in $L((q))$ generated over $L$ by the image of $F_0$ under the coefficientwise ring map $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$. Let $\iota$ be a finite index type and let $x : \iota \to \overline{\mathbb{Q}}((q))$ be a family of Laurent series over the algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ such that $x_i \in \overline{\mathbb{Q}}\cdot F_0$ for every $i$. The assertion is that there exists an intermediate field $E$ of $\mathbb{Q}$ in $\overline{\mathbb{Q}}$ which is finite-dimensional over $\mathbb{Q}$ and Galois over $\mathbb{Q}$, together with a family $y : \iota \to E((q))$ such that $y_i \in E \cdot F_0$ for every $i$ and the coefficientwise map $E((q)) \to \overline{\mathbb{Q}}((q))$ induced by the inclusion $E \hookrightarrow \overline{\mathbb{Q}}$ sends $y_i$ to $x_i$ for every $i$.
--
--   A field-of-definition statement: finitely many elements of the base change of $F_0$ to $\overline{\mathbb{Q}}$ already lie in the base change to a single finite Galois extension of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$. No hypothesis is placed on $F_0$; it is used in the passage from $\overline{\mathbb{Q}}$-coefficients to coefficients in a number field in [`ModularCurve.exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card`](thm.html#ModularCurve.exists_linearIndependent_isModPFormFn_rat_dimFormula_le_card).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_isGalois_forall_coeffMap_eq_of_mem_laurentBaseChange
    (F₀ : IntermediateField ℚ (LaurentSeries ℚ)) {ι : Type} [Finite ι]
    (x : ι → LaurentSeries (AlgebraicClosure ℚ))
    (hx : ∀ i, x i ∈ laurentBaseChange (AlgebraicClosure ℚ) F₀) :
    ∃ E : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ E ∧ IsGalois ℚ E ∧
      ∃ y : ι → LaurentSeries E, (∀ i, y i ∈ laurentBaseChange E F₀) ∧
        ∀ i, coeffMap (algebraMap E (AlgebraicClosure ℚ)) (y i) = x i := by sorry
