-- Prove2me | Theorems.Thm_OAI_NCHitting_no_polynomial_log_primitive
-- name    : OAI.NCHitting.no_polynomial_log_primitive
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:16:50.687595+00:00
-- url     : https://prove2.me/theorems/775d826a-6068-4d11-af08-09a0308db407
-- title:
--   The derivative of a rational function has no simple-pole part: all residues $c_i$ vanish
-- statement:
--   Let $F$ be a field of characteristic zero and $(a_i)_{i\in\iota}$ a finite family of pairwise distinct elements of $F$. Write $\pi(X)=\prod_i(X-a_i)$ and $\pi_i(X)=\prod_{j\ne i}(X-a_j)$. Let $p_0,p\in F[X]$ with $p_0\ne0$, and let $c_i\in F$. If
--   $$
--   \pi\,\bigl(p_0\,p'-p_0'\,p\bigr)+p_0^2\sum_{i}c_i\,\pi_i=0,
--   $$
--   then $c_i=0$ for every $i$.
--
--   Dividing by $\pi\,p_0^2$, the hypothesis says
--   $$
--   \Bigl(\frac{p}{p_0}\Bigr)'=-\sum_i\frac{c_i}{X-a_i}.
--   $$
--   The lemma states that a sum of simple fractions with distinct poles is the derivative of a rational function only when it is zero; that is, $\log(X-a_i)$ has no rational primitive. It drives the linear independence of the word series.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Independence.lean#L207-L225

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

open OAI OAI.NCHitting
open Polynomial
variable {F : Type*} [Field F] [CharZero F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem OAI.NCHitting.no_polynomial_log_primitive (a : ι → F) (ha : Function.Injective a)
    (p0 p : F[X]) (hp0 : p0 ≠ 0) (c : ι → F)
    (h : poleProduct a * (p0 * p.derivative - p0.derivative * p) +
      p0^2 * (∑ i, Polynomial.C (c i) * puncturedPoleProduct a i) = 0) :
    ∀ i, c i = 0 := by sorry
