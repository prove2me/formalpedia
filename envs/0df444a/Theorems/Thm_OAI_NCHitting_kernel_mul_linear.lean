-- Prove2me | Theorems.Thm_OAI_NCHitting_kernel_mul_linear
-- name    : OAI.NCHitting.kernel_mul_linear
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:13:42.236824+00:00
-- url     : https://prove2.me/theorems/aacf6f2a-4fb7-4a61-8d6c-6c9ec7aa19bd
-- title:
--   The power series $\sum_r (-1)^r X^r/i^{r+1}$ is the inverse of $X+i$
-- statement:
--   Let $F$ be a field of characteristic zero and $i\ge1$ a natural number. Let
--   $$
--   \kappa_i=\sum_{r\ge0}\frac{(-1)^r}{i^{\,r+1}}X^r\in F[[X]].
--   $$
--   Then
--   $$
--   \kappa_i\cdot(X+i)=1 .
--   $$
--
--   So $\kappa_i$ is the power series expansion of $1/(X+i)$ around $0$. This identifies the kernels of the iterated integrals with simple rational functions with poles at $-i$, and lets differential equations with these kernels be cleared of denominators.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Series.lean#L134-L149

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
import Definitions.Def_OAI_Algebra_FormulaHitting_Multiplicity
import Definitions.Def_OAI_Algebra_FormulaHitting_Formula
import Definitions.Def_OAI_Algebra_FormulaHitting_Representation
import Definitions.Def_OAI_Algebra_FormulaHitting_Series

open OAI OAI.NCHitting
open PowerSeries
variable {F : Type*} [Field F] [CharZero F]

theorem OAI.NCHitting.kernel_mul_linear (i : ℕ) (hi : i ≠ 0) :
    kernel (F := F) i * (PowerSeries.X + PowerSeries.C (i : F)) = 1 := by sorry
