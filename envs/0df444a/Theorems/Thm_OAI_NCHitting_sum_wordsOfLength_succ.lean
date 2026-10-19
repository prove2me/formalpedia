-- Prove2me | Theorems.Thm_OAI_NCHitting_sum_wordsOfLength_succ
-- name    : OAI.NCHitting.sum_wordsOfLength_succ
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:11:36.71963+00:00
-- url     : https://prove2.me/theorems/18405ac7-f94c-45da-bb2e-232c9d009b13
-- title:
--   Summing over words of length $k+1$ by first letter
-- statement:
--   Let $n,k\in\mathbb{N}$, let $M$ be an additive commutative monoid, and let $f$ be a function from words over the alphabet $\{0,\dots,n-1\}$ to $M$. Let $\mathcal W_k$ denote the finite set of words of length $k$. Then
--   $$
--   \sum_{w\in\mathcal W_{k+1}}f(w)=\sum_{i=0}^{n-1}\ \sum_{w\in\mathcal W_k}f(i\,w),
--   $$
--   where $i\,w$ is the word with first letter $i$ followed by $w$.
--
--   This is the recursion used to expand sums over all words of a given length, for example when comparing products of transition matrices with iterated integrals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Formula.lean#L109-L124

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

open OAI OAI.NCHitting

theorem OAI.NCHitting.sum_wordsOfLength_succ {M : Type*} [AddCommMonoid M]
    {n : ℕ} (k : ℕ) (f : Word n → M) :
    (∑ w ∈ wordsOfLength n (k + 1), f w) =
      ∑ i : Fin n, ∑ w ∈ wordsOfLength n k, f (i :: w) := by sorry
