-- Prove2me | Theorems.Thm_OAI_NCHitting_polynomialEncode_eq_zero
-- name    : OAI.NCHitting.polynomialEncode_eq_zero
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:17:40.215526+00:00
-- url     : https://prove2.me/theorems/c52eb39d-2a63-4732-8d5f-ffbf4647b37a
-- title:
--   The word series $\Phi(w)$ are linearly independent over the polynomial ring
-- statement:
--   Let $F$ be a field of characteristic zero and $n\in\mathbb{N}$. For a word $w$ over $\{0,\dots,n-1\}$, let $\Phi(w)\in F[[X]]$ be the iterated integral
--   $$
--   \Phi(\varepsilon)=1,\qquad \Phi(iw)=\int_0^X\Phi(w)\,\frac{dX}{X+i+1}.
--   $$
--   Let $c=(c_w)_w$ be a finitely supported family of polynomials $c_w\in F[X]$. Suppose $c_w\ne0$ only for words of length $|w|\le D$, for some $D\in\mathbb{N}$. If
--   $$
--   \sum_{w}c_w\,\Phi(w)=0\quad\text{in }F[[X]],
--   $$
--   then $c_w=0$ for every word $w$.
--
--   So the iterated integrals $\Phi(w)$ attached to distinct words are linearly independent over $F[X]$, and in particular over $F$. Consequently a noncommutative polynomial is determined by the single power series $\sum_wf_w\Phi(w)$.
--
--   **Formalization Note** The family $c$ is an element of `PolyWords F n = List (Fin n) →₀ F[X]`. The hypothesis is `polynomialEncode c = 0`, and `LengthBound D c` is the length bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/WordIndependence.lean#L227-L317

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
import Definitions.Def_OAI_Algebra_FormulaHitting_FormulaSeries
import Definitions.Def_OAI_Algebra_FormulaHitting_Independence
import Definitions.Def_OAI_Algebra_FormulaHitting_WordIndependence

open OAI OAI.NCHitting
open Polynomial PowerSeries
variable {F : Type*} [Field F] [CharZero F] {n : ℕ}

theorem OAI.NCHitting.polynomialEncode_eq_zero (D : ℕ) (c : PolyWords F n)
    (hc : LengthBound D c) (he : polynomialEncode c = 0) : c = 0 := by sorry
