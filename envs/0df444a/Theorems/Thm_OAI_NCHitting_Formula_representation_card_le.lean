-- Prove2me | Theorems.Thm_OAI_NCHitting_Formula_representation_card_le
-- name    : OAI.NCHitting.Formula.representation_card_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:12:14.212803+00:00
-- url     : https://prove2.me/theorems/01533c38-c3c7-4514-9d0e-49f17bc649d7
-- title:
--   The automaton of a formula has at most twice its size many states
-- statement:
--   Fix $n\in\mathbb{N}$. Words are finite lists $w=w_1\cdots w_m$ of letters in $\{0,\dots,n-1\}$, with length $|w|=m$. A noncommutative formula $f$ over $F$ in variables $x_0,\dots,x_{n-1}$ is built from scalars $a\in F$, variables $x_i$, binary sums and binary products. Its size counts each leaf as $1$ and each internal node as $1$ plus the sizes of its two parts.
--
--   Every formula $f$ is translated recursively into an acyclic weighted automaton:
--
--   - a scalar gets $1$ state;
--   - a variable gets $2$ states;
--   - for a sum or product, the state set is the disjoint union of the state sets of the two parts.
--
--   For every such formula over a commutative semiring, the number $m(f)$ of states satisfies
--   $$
--   m(f)\le 2\,\operatorname{size}(f).
--   $$
--
--   The automaton dimension is thus linear in the formula size. This keeps the multiplicity bound, and hence the size of the hitting matrices, polynomial in $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Representation.lean#L302-L316

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

theorem OAI.NCHitting.Formula.representation_card_le {F : Type*} {n : ℕ} [CommSemiring F]
    (f : Formula F n) : Fintype.card f.representation.State ≤ 2 * f.size := by sorry
