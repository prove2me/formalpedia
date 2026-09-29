-- Prove2me | Theorems.Thm_ModularCurve_exists_numberField_presentation
-- name    : ModularCurve.exists_numberField_presentation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/650c9620-d143-5872-81fc-1e37f9635113
-- title:
--   Number field presentation of functions on X₀(q)_ℚ̄
-- statement:
--   Let $q$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$ (realised as `AlgebraicClosure ℚ`), and let $f$ be an element of `modularFunctionFieldBar (1 * q)`, that is, of the intermediate field of $\overline{\mathbb Q} \subseteq \mathrm{LaurentSeries}(\overline{\mathbb Q})$ obtained by adjoining to $\overline{\mathbb Q}$ the image, under the coefficientwise embedding `coeffEmb`, of the field `modularFunctionFieldFull (1 * q)` generated over $\mathbb Q$ inside $\mathrm{LaurentSeries}(\mathbb Q)$ by the set `divisorExpansions (1 * q)` (the level is written $1 \cdot q$ throughout, not reduced). Then there exist an intermediate field $K$ of $\mathbb Q \subseteq \overline{\mathbb Q}$ which is finite-dimensional over $\mathbb Q$, i.e. a number field, and two polynomials $P, Q$ in two variables with coefficients in the subring `coeffSubring A K` $= A \cap K$ of $\overline{\mathbb Q}$, such that, writing $E$ for the ring homomorphism `modularEval (1 * q) (coeffSubring A K)` which sends a coefficient to the corresponding constant Laurent series and the two variables to `jqModC` (the series $q^{-1}$ times the image of the integral power series `jNum`, the $q$-expansion of $j$) and to `jqNModC` of level $1 \cdot q$ (the substitution $q \mapsto q^{1 \cdot q}$ applied to `jqModC`), one has $E(Q) \neq 0$ and $f \cdot E(Q) = E(P)$ inside $\mathrm{LaurentSeries}(\overline{\mathbb Q})$.
--
--   This records that every element of the function field of $X_0(q)$ over $\overline{\mathbb Q}$, presented through $q$-expansions, is a quotient of two-variable polynomials in the $q$-expansions of $j$ and $j_q$ whose coefficients lie in $A \cap K$ for a single number field $K$, with a nonvanishing denominator. It opens the descent from $\overline{\mathbb Q}$ to a number field used in the local study of the nodes of $X_0(q)$ in characteristic $q$, and is cited by the two-branch normalisation statements and by the construction of a finite-dimensional field over which a given function and its reduction are defined.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_numberField_presentation.lean

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

theorem ModularCurve.exists_numberField_presentation
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (f : ↥(modularFunctionFieldBar (1 * q))) :
    ∃ (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (_ : FiniteDimensional ℚ K)
      (P Q : MvPolynomial (Fin 2) (coeffSubring A K)),
      modularEval (1 * q) (coeffSubring A K) Q ≠ 0 ∧
      (f : LaurentSeries (AlgebraicClosure ℚ)) * modularEval (1 * q) (coeffSubring A K) Q
        = modularEval (1 * q) (coeffSubring A K) P := by sorry
