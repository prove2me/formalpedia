-- Prove2me | Theorems.Thm_ModularCurve_exists_numberField_presentation_level
-- name    : ModularCurve.exists_numberField_presentation_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/86ef2979-17a0-51f6-9c9b-558a1bf26a93
-- title:
--   Number-field presentation of functions on X₀(Nq)
-- statement:
--   Let $q$ be a prime, let $N$ be a nonzero natural number, and let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`. Let $f$ be an element of `modularFunctionFieldBar (N * q)`, that is, of the subfield of the Laurent series field $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the image under the coefficientwise embedding `coeffEmb` of the subfield `modularFunctionFieldFull (N * q)` of $\mathbb Q((q))$, the latter being generated over $\mathbb Q$ by the divisor expansions of level $Nq$. Then there are an intermediate field $K$ of $\overline{\mathbb Q}/\mathbb Q$ that is finite-dimensional over $\mathbb Q$, and two polynomials $P, Q$ in two variables over the subring $A \cap K$ of $\overline{\mathbb Q}$ (`coeffSubring A K`), such that, writing $E$ for the ring homomorphism `modularEval (N * q)` which sends a polynomial to its value at the pair of Laurent series $\bigl(j(q), j(q^{Nq})\bigr)$, namely `jqModC` $= q^{-1}\cdot(\text{numerator of }j)$ and its substitution `jqNModC` at level $Nq$, with coefficients viewed as constant series, one has $E(Q) \neq 0$ and $f \cdot E(Q) = E(P)$ in $\overline{\mathbb Q}((q))$.
--
--   This is the statement that every element of the function field of $X_0(Nq)$ over $\overline{\mathbb Q}$, realised as a Laurent series in $q$, is a quotient of two polynomials in $j(q)$ and $j(q^{Nq})$ whose coefficients lie in a single number field $K$ and, moreover, in the valuation subring $A$ intersected with $K$; in particular $f$ lies in $K(j, j_{Nq})$. It serves the descent to a number field in the analysis of nodal reduction of modular curves, and is used in the construction of node packages and of integral models over prolongation data, as well as in the integrality statement for $j$ on affine bases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_numberField_presentation_level.lean

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

theorem ModularCurve.exists_numberField_presentation_level
    {q : ℕ} [Fact q.Prime] {N : ℕ} [NeZero N] (A : ValuationSubring (AlgebraicClosure ℚ))
    (f : ↥(modularFunctionFieldBar (N * q))) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (P Q : MvPolynomial (Fin 2) (coeffSubring A K)),
      modularEval (N * q) (coeffSubring A K) Q ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (N * q) (coeffSubring A K) Q
        = modularEval (N * q) (coeffSubring A K) P := by sorry
