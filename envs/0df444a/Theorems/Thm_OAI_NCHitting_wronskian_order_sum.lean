-- Prove2me | Theorems.Thm_OAI_NCHitting_wronskian_order_sum
-- name    : OAI.NCHitting.wronskian_order_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:06:51.247715+00:00
-- url     : https://prove2.me/theorems/d04bd572-3cd0-40bf-aacd-e2612d3df80d
-- title:
--   The Wronskian of power series with distinct orders is nonzero of order $\sum_l a_l-\binom{k}{2}$
-- statement:
--   Let $F$ be a field of characteristic zero and $k\in\mathbb{N}$. Let $b_0,\dots,b_{k-1}\in F[[X]]$ be power series and $a_0,\dots,a_{k-1}\in\mathbb{N}$ pairwise distinct. Assume each $b_l$ has order exactly $a_l$: $[X^{a_l}]b_l\ne0$ and $[X^r]b_l=0$ for all $r<a_l$. Let
--   $$
--   W(b)=\det\bigl(D^jb_l\bigr)_{0\le j,l<k}
--   $$
--   be the Wronskian, where $D^j$ is the $j$-th formal derivative. Then $W(b)\ne0$, and its order $\operatorname{ord}W(b)$ (the index of its first nonzero coefficient) satisfies
--   $$
--   \operatorname{ord}W(b)+\sum_{j=0}^{k-1}j=\sum_{l=0}^{k-1}a_l .
--   $$
--
--   So the Wronskian of power series with distinct orders is nonzero, with order exactly $\sum_la_l-\binom{k}{2}$. This gives a sharp count of how much a Wronskian vanishes at the origin.
--
--   **Formalization Note** The order of a power series is an element of $\mathbb{N}\cup\{\infty\}$. The statement uses its natural-number truncation `order.toNat`, which is the true order because $W(b)\ne0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/FormulaHitting/Wronskian.lean#L163-L190

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

open OAI OAI.NCHitting
open PowerSeries Matrix
variable {F : Type*} [Field F]

theorem OAI.NCHitting.wronskian_order_sum [CharZero F] {k : ℕ} (b : Fin k → PowerSeries F)
    (a : Fin k → ℕ) (ha : Function.Injective a)
    (hb : ∀ l, PowerSeries.coeff (a l) (b l) ≠ 0)
    (hz : ∀ l r, r < a l → PowerSeries.coeff r (b l) = 0) :
    wronskian b ≠ 0 ∧
      (wronskian b).order.toNat + (∑ j : Fin k, j.val) = ∑ l : Fin k, a l := by sorry
