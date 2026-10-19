-- Prove2me | Theorems.Thm_OAI_NCHitting_sum_eq_sum_wordsOfLength
-- name    : OAI.NCHitting.sum_eq_sum_wordsOfLength
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:14:15.515832+00:00
-- url     : https://prove2.me/theorems/4da68398-f830-455d-b4b6-af3c08fff974
-- title:
--   Sums over a finitely supported word family split by word length
-- statement:
--   Let $n,d\in\mathbb{N}$, let $F$ be a type with zero, and let $M$ be an additive commutative monoid. Let $p$ be a finitely supported function from words over $\{0,\dots,n-1\}$ to $F$ with $p(w)=0$ whenever $|w|\ge d$. Let $h(w,x)\in M$ be defined for words $w$ and $x\in F$, with $h(w,0)=0$. Writing $\mathcal W_k$ for the set of words of length $k$,
--   $$
--   \sum_{w\in\operatorname{supp}p}h\bigl(w,p(w)\bigr)=\sum_{k=0}^{d-1}\ \sum_{w\in\mathcal W_k}h\bigl(w,p(w)\bigr).
--   $$
--
--   This converts the sum over the support of a noncommutative polynomial, such as the coefficients of a formula, into an explicit sum over words of each length below a cutoff.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Evaluation.lean#L56-L76

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
import Definitions.Def_OAI_Algebra_FormulaHitting_System
import Definitions.Def_OAI_Algebra_FormulaHitting_Evaluation

open OAI OAI.NCHitting
attribute [local instance] OAI.NCHitting.instDecidableEqFreeMonoidFin_oAI

theorem OAI.NCHitting.sum_eq_sum_wordsOfLength {F M : Type*} {n d : ℕ}
    [Zero F] [AddCommMonoid M] (p : Word n →₀ F)
    (hcut : ∀ w, d ≤ w.length → p w = 0)
    (h : Word n → F → M) (hzero : ∀ w, h w 0 = 0) :
    p.sum h = ∑ k ∈ Finset.range d, ∑ w ∈ wordsOfLength n k, h w (p w) := by sorry
