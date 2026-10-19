-- Prove2me | Theorems.Thm_OAI_NCHitting_natDegree_det_le_sum
-- name    : OAI.NCHitting.natDegree_det_le_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:08:33.032712+00:00
-- url     : https://prove2.me/theorems/c5567503-dde9-4805-bdb1-c36342976826
-- title:
--   Degree of a polynomial determinant is at most the sum of the row degree bounds
-- statement:
--   Let $F$ be a field and $I$ a finite index set with decidable equality. Let $A=(A_{ij})_{i,j\in I}$ be a square matrix of polynomials in $F[X]$, and let $d:I\to\mathbb{N}$ be such that every entry of row $i$ has degree at most $d_i$:
--   $$
--   \deg A_{ij}\le d_i\qquad\text{for all } i,j\in I.
--   $$
--   Then
--   $$
--   \deg\det A\le\sum_{i\in I}d_i .
--   $$
--
--   This bound is used to control the degree of Wronskian-type determinants whose rows come from successive derivatives.
--
--   **Formalization Note** Degrees are `natDegree`, so the zero polynomial has degree $0$ and the statement is trivially true when $\det A=0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Minors.lean#L54-L69

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
open Matrix Finset Polynomial
variable {R : Type*} [CommRing R]
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

theorem OAI.NCHitting.natDegree_det_le_sum {F : Type*} [Field F]
    (A : Matrix I I F[X]) (d : I → ℕ)
    (h : ∀ i j, (A i j).natDegree ≤ d i) :
    A.det.natDegree ≤ ∑ i, d i := by sorry
