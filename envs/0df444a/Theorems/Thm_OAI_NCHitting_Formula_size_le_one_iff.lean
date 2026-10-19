-- Prove2me | Theorems.Thm_OAI_NCHitting_Formula_size_le_one_iff
-- name    : OAI.NCHitting.Formula.size_le_one_iff
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:11:12.579506+00:00
-- url     : https://prove2.me/theorems/77052ac9-b46e-41f8-870c-5569176d4dcb
-- title:
--   A formula has size at most one exactly when it is a scalar or a variable
-- statement:
--   Fix $n\in\mathbb{N}$. Words are finite lists $w=w_1\cdots w_m$ of letters in $\{0,\dots,n-1\}$, with length $|w|=m$. A noncommutative formula $f$ over $F$ in variables $x_0,\dots,x_{n-1}$ is built from scalars $a\in F$, variables $x_i$, binary sums and binary products. Its size counts each leaf as $1$ and each internal node as $1$ plus the sizes of its two parts.
--
--   For every formula $f$ over any type of scalars,
--   $$
--   \operatorname{size}(f)\le1\iff f=a\ \text{for some scalar }a,\ \text{ or }\ f=x_i\ \text{for some } i .
--   $$
--
--   This classifies the formulas allowed in the degenerate case $s=1$ of the hitting-set theorem, which is handled directly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Formula.lean#L29-L49

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

open OAI OAI.NCHitting OAI.NCHitting.Formula

theorem OAI.NCHitting.Formula.size_le_one_iff {F : Type*} {n : ℕ} (f : Formula F n) :
    f.size ≤ 1 ↔ (∃ a, f = scalar a) ∨ (∃ i, f = var i) := by sorry
