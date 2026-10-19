-- Prove2me | Theorems.Thm_OAI_NCHitting_hasOrderBasis_of_finrank_le
-- name    : OAI.NCHitting.hasOrderBasis_of_finrank_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:08:08.370543+00:00
-- url     : https://prove2.me/theorems/33eaea41-f936-4906-b7ef-d914a48b75e6
-- title:
--   Every finite-dimensional space of power series has a basis with distinct orders
-- statement:
--   Let $F$ be a field and $N\in\mathbb{N}$. Let $V\subseteq F[[X]]$ be a finite-dimensional $F$-linear subspace with $\dim_FV\le N$. Then $V$ has an order basis: there are $k$, power series $b_0,\dots,b_{k-1}$ and pairwise distinct $a_0,\dots,a_{k-1}\in\mathbb{N}$ such that the $b_i$ are linearly independent and span $V$, and each $b_i$ has order exactly $a_i$:
--   $$
--   [X^{a_i}]\,b_i\ne0,\qquad [X^r]\,b_i=0\ \ (r<a_i).
--   $$
--
--   This is Gaussian elimination for power series ordered by vanishing order. It shows that the set of orders of nonzero elements of $V$ has exactly $\dim V$ elements, and it supplies the input for Wronskian computations.
--
--   **Formalization Note** The bound $N$ is the induction parameter, so the theorem covers every finite-dimensional subspace by taking $N=\dim V$. No characteristic assumption is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/OrderBasis.lean#L31-L122

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.FreeMonoid.Basic
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Cast.Lemmas
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Polynomial.Wronskian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_FormulaHitting
import Definitions.Def_OAI_Algebra_FormulaHitting_Wronskian
import Definitions.Def_OAI_Algebra_FormulaHitting_NumeratorRows
import Definitions.Def_OAI_Algebra_FormulaHitting_OrderBasis

open OAI OAI.NCHitting
open PowerSeries Submodule
variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem OAI.NCHitting.hasOrderBasis_of_finrank_le (N : ℕ) :
    ∀ (V : Submodule F (PowerSeries F)) [FiniteDimensional F V],
      Module.finrank F V ≤ N → HasOrderBasis V := by sorry
