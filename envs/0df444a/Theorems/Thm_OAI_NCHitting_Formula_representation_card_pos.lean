-- Prove2me | Theorems.Thm_OAI_NCHitting_Formula_representation_card_pos
-- name    : OAI.NCHitting.Formula.representation_card_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:12:32.954187+00:00
-- url     : https://prove2.me/theorems/c05fff3a-aed7-41be-adbf-f580d7d87187
-- title:
--   The automaton of a formula has at least one state
-- statement:
--   Fix $n\in\mathbb{N}$. Words are finite lists $w=w_1\cdots w_m$ of letters in $\{0,\dots,n-1\}$, with length $|w|=m$. A noncommutative formula $f$ over $F$ in variables $x_0,\dots,x_{n-1}$ is built from scalars $a\in F$, variables $x_i$, binary sums and binary products. Its size counts each leaf as $1$ and each internal node as $1$ plus the sizes of its two parts.
--
--   Every formula is translated recursively into an acyclic weighted automaton: a scalar gets $1$ state, a variable $2$ states, and sums and products the disjoint union of the state sets of their parts. For every formula $f$ over a commutative semiring, the number of states is positive:
--   $$
--   m(f)\ge1 .
--   $$
--
--   A nonempty state set is needed for the fundamental matrix of the automaton's differential system to be an invertible matrix.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Representation.lean#L318-L330

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

open OAI OAI.NCHitting
open Matrix

theorem OAI.NCHitting.Formula.representation_card_pos {F : Type*} {n : ℕ} [CommSemiring F]
    (f : Formula F n) : 0 < Fintype.card f.representation.State := by sorry
