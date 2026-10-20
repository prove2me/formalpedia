-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_truncatedExcess_le_original
-- name    : OAI.TalagrandThreshold.Selector.truncatedExcess_le_original
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:52:03.040696+00:00
-- url     : https://prove2.me/theorems/b0d2298f-d7f9-4219-82bf-2b5b0d98ab28
-- title:
--   Truncation does not increase the excess when heavy points are inside
-- statement:
--   Let $X$ be finite, $w:X\to\mathbb{R}$, $A\subseteq X$, $d\ge0$ and $u\in\mathbb{R}$, and suppose every $x$ with $w(x)>u$ lies in $A$. Then
--   $$
--   \sum_x\min(w(x),u)\bigl([x\in A]-(1-d)\bigr)\le\sum_xw(x)\bigl([x\in A]-(1-d)\bigr) .
--   $$
--
--   Restoring the truncated weights only changes heavy points. These lie in $A$, where the coefficient $d$ is nonnegative.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorFeasibility.lean#L130-L147

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Find
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Order.Compact
import Definitions.Def_TalagrandExpectationThreshold
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Model
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_Basic
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMasses
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityFinite
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityProduct
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingExpectation
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ProbabilityColors
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_ScaleBounds
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorTruncationDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDefinitions
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorFeasibility

open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

theorem OAI.TalagrandThreshold.Selector.truncatedExcess_le_original (w : α → ℝ) (A : Finset α) (d u : ℝ)
    (hd : 0 ≤ d) (hheavy : ∀ x, u < w x → x ∈ A) :
    truncatedExcess w A d u ≤
      ∑ x, w x * ((if x ∈ A then 1 else 0) - (1 - d)) := by sorry
