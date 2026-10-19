-- Prove2me | Theorems.Thm_OAI_NCHitting_formal_residue_obstruction
-- name    : OAI.NCHitting.formal_residue_obstruction
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:16:21.91512+00:00
-- url     : https://prove2.me/theorems/7bac8abf-5f4b-443a-affd-2edf5978dafb
-- title:
--   A derivative has no residue: the residue obstruction for $p_0^2(p/p_0)'=-S/(XQ)$
-- statement:
--   Let $F$ be a field of characteristic zero and $p_0,p,Q,S\in F[[X]]$ with $p_0\ne0$ and $Q(0)\ne0$. Assume
--   $$
--   X\,Q\,\bigl(p_0\,p'-p_0'\,p\bigr)+p_0^2\,S=0 .
--   $$
--   Then $S(0)=0$.
--
--   Formally, $(p/p_0)'=-S/(XQ)$. The left side is the derivative of a Laurent series and so has no $X^{-1}$ term, while the right side has residue $-S(0)/Q(0)$. The lemma is the power-series form of this residue argument. It is used to show that a rational function's derivative cannot contain a nonzero multiple of $1/(X-a)$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Independence.lean#L100-L147

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
open PowerSeries

theorem OAI.NCHitting.formal_residue_obstruction (p0 p Q S : PowerSeries F)
    (hp0 : p0 ≠ 0) (hQ : PowerSeries.constantCoeff Q ≠ 0)
    (h : (PowerSeries.X * Q) *
        (p0 * PowerSeries.derivative (R := F) p - PowerSeries.derivative (R := F) p0 * p) +
        p0^2 * S = 0) : PowerSeries.constantCoeff S = 0 := by sorry
