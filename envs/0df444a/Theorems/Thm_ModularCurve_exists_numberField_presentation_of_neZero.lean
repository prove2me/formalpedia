-- Prove2me | Theorems.Thm_ModularCurve_exists_numberField_presentation_of_neZero
-- name    : ModularCurve.exists_numberField_presentation_of_neZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/91b59b66-e3dc-5f55-84dd-d1b484506c69
-- title:
--   Number field presentation of modular functions in j, j_N
-- statement:
--   Let $N \ge 1$, let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, and let $f$ belong to `modularFunctionFieldBar N`, the intermediate field of the Laurent series field $\overline{\mathbb Q}((\mathfrak q))$ over $\overline{\mathbb Q}$ obtained by adjoining to $\overline{\mathbb Q}$ the image under the coefficient embedding `coeffEmb` of `modularFunctionFieldFull N`, itself the subfield of $\mathbb Q((\mathfrak q))$ generated over $\mathbb Q$ by the set `divisorExpansions N`. Then there exist an intermediate field $K$ of $\overline{\mathbb Q}/\mathbb Q$ that is finite-dimensional over $\mathbb Q$, i.e. a number field inside $\overline{\mathbb Q}$, and two polynomials $P, Q$ in two variables with coefficients in `coeffSubring A K`, the subring $A \cap K$ of $\overline{\mathbb Q}$, such that, writing $\mathrm{ev}$ for the ring homomorphism `modularEval N` that sends a coefficient to the corresponding constant Laurent series, the variable $0$ to $\mathfrak q^{-1}\cdot$`jNum`$\, = j(\mathfrak q)$ and the variable $1$ to its $N$-fold $\mathfrak q$-expansion $j(\mathfrak q^{N})$, one has $\mathrm{ev}(Q) \ne 0$ and $f \cdot \mathrm{ev}(Q) = \mathrm{ev}(P)$ as Laurent series over $\overline{\mathbb Q}$.
--
--   This is the descent statement that every element of the function field of $X_0(N)$ over $\overline{\mathbb Q}$ is a quotient of two polynomials in $j(\mathfrak q)$ and $j(\mathfrak q^{N})$ whose coefficients lie in the intersection of a given valuation ring of $\overline{\mathbb Q}$ with a single number field; in particular $f \in K(j, j_N)$. It serves the later reduction and specialisation arguments, being cited in the study of models in characteristic $\ell$ and of prolongations of places along $j$-integral data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_numberField_presentation_of_neZero.lean

import Mathlib
import Definitions.Def_ModularCurve_NodeLocalized
import Definitions.Def_ModularCurve_NodeDescent
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open ModularCurve.NodeLocalized

theorem ModularCurve.exists_numberField_presentation_of_neZero
    {N : ℕ} [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (f : ↥(modularFunctionFieldBar N)) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (P Q : MvPolynomial (Fin 2) (coeffSubring A K)),
      modularEval N (coeffSubring A K) Q ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval N (coeffSubring A K) Q
        = modularEval N (coeffSubring A K) P := by sorry
