-- Prove2me | Theorems.Thm_OAI_CirculantHadamard_integerCyclotomicEvaluation_coefficientPolynomial
-- name    : OAI.CirculantHadamard.integerCyclotomicEvaluation_coefficientPolynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T09:26:52.967988+00:00
-- url     : https://prove2.me/theorems/b5e51a91-75fa-4619-b63b-a397d5ee4556
-- title:
--   Cyclotomic evaluation of an integer group-ring element as a polynomial class
-- statement:
--   Let $A$ be a commutative ring, $n>0$, and $T\in\mathbb Z[\mathbb Z/n]$. Evaluating $T$ in $A[X]/(\Phi_n(X))$ at the class $\zeta$ of $X$ gives the class of its coefficient polynomial:
--   $$
--   \sum_{a\in\mathbb Z/n}T(a)\,\zeta^{a}=\Bigl[\sum_{i<n}T(i)\,X^i\Bigr]\quad\text{in }A[X]/(\Phi_n(X)).
--   $$
--
--   This turns questions about the cyclotomic value of $T$ into questions about an explicit polynomial with the coefficients of $T$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/LinearAlgebra/CirculantHadamard/OrderCyclotomicDivisibility.lean#L28-L50

import Mathlib
import Definitions.Def_CirculantHadamard
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Basic
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_Witnesses
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_MatrixBridge
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicRing
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicNorm
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicProjection
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_LocalDVR
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_IntegerTwoLocal
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclicPolynomial
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedConjugation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_CyclotomicIntegerEvaluation
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_DyadicRemainder
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedEisenstein
import Definitions.Def_OAI_LinearAlgebra_CirculantHadamard_RamifiedLocal

open OAI OAI.CirculantHadamard
universe uA
open Polynomial
open scoped BigOperators

theorem OAI.CirculantHadamard.integerCyclotomicEvaluation_coefficientPolynomial
    (A : Type uA) [CommRing A] (n : ℕ) [NeZero n] (T : CyclicRing.Elem ℤ n) :
    integerCyclotomicEvaluation A n T =
      AdjoinRoot.mk (cyclotomic n A)
        (DyadicRemainder.coefficientPolynomial n
          (fun i => algebraMap ℤ A (T.coeff (i : ZMod n)))) := by sorry
