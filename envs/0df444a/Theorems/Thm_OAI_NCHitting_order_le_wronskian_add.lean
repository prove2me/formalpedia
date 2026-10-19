-- Prove2me | Theorems.Thm_OAI_NCHitting_order_le_wronskian_add
-- name    : OAI.NCHitting.order_le_wronskian_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:08:51.669274+00:00
-- url     : https://prove2.me/theorems/4594ce67-66ee-464a-a91a-9299464ed785
-- title:
--   Orders of elements in the span of power series are bounded by the Wronskian's order plus $k-1$
-- statement:
--   Let $F$ be a field and $k\in\mathbb{N}$. Let $b_0,\dots,b_{k-1}\in F[[X]]$ have nonzero Wronskian
--   $$
--   W(b)=\det\bigl(D^jb_l\bigr)_{0\le j,l<k}\neq0,
--   $$
--   where $D^j$ is the $j$-th formal derivative. Let $y\ne0$ be an $F$-linear combination of $b_0,\dots,b_{k-1}$. Then
--   $$
--   \operatorname{ord}y\le\operatorname{ord}W(b)+k-1,
--   $$
--   where $\operatorname{ord}$ is the index of the first nonzero coefficient.
--
--   Every nonzero element of a $k$-dimensional space of power series therefore vanishes at $0$ to order at most $\operatorname{ord}W+k-1$. Upper bounds on the Wronskian's order thus become bounds on how much any element of the span can vanish.
--
--   **Formalization Note** Orders are taken as natural numbers via `order.toNat`; both $y$ and $W(b)$ are nonzero, so these are the true orders. The right-hand side uses truncated natural-number subtraction, which is harmless here since $k\ge1$ whenever $y\ne0$. No characteristic assumption is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/WronskianBound.lean#L33-L72

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
open PowerSeries Matrix Submodule
variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem OAI.NCHitting.order_le_wronskian_add {k : ℕ} (b : Fin k → PowerSeries F)
    (hb : wronskian b ≠ 0) (y : PowerSeries F) (hy : y ≠ 0)
    (hspan : y ∈ Submodule.span F (Set.range b)) :
    y.order.toNat ≤ (wronskian b).order.toNat + k - 1 := by sorry
