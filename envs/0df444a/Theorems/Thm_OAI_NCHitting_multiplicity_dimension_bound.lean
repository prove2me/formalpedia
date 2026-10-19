-- Prove2me | Theorems.Thm_OAI_NCHitting_multiplicity_dimension_bound
-- name    : OAI.NCHitting.multiplicity_dimension_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:10:40.235281+00:00
-- url     : https://prove2.me/theorems/9d8c9d44-2088-40d8-b359-ba070e8f1b6e
-- title:
--   The arithmetic bound $(n-1)\binom{m}{2}+m\le 2ns^2$ for $m\le 2s$
-- statement:
--   Let $n,s\ge1$ and $m\le2s$ be natural numbers. Then
--   $$
--   (n-1)\binom{m}{2}+m\le 2ns^2 .
--   $$
--
--   Here $m$ is the number of states of the automaton of a formula of size at most $s$ (at most $2s$), and $2ns^2$ is the size of the hitting matrices. The inequality says that the multiplicity bound for a nonzero formula series lies below the matrix size, so a jet of that length detects it.
--
--   **Formalization Note** All quantities are natural numbers, and $n-1$ is truncated subtraction, exact since $n\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/DimensionBound.lean#L19-L39

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

open OAI OAI.NCHitting

theorem OAI.NCHitting.multiplicity_dimension_bound {n s m : ℕ}
    (hn : 0 < n) (hs : 0 < s) (hm : m ≤ 2*s) :
    (n-1)*m.choose 2 + m ≤ 2*n*s^2 := by sorry
