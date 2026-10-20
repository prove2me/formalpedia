-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_sum_wordCount_weight
-- name    : OAI.TalagrandThreshold.sum_wordCount_weight
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:54:28.093676+00:00
-- url     : https://prove2.me/theorems/7ed2325d-ed07-4278-9e40-94e2ecbfef85
-- title:
--   The multinomial identity via word counts
-- statement:
--   Let $H$ be finite, $t\in\mathbb{N}$ and $\pi:H\to\mathbb{R}$. With $W_t(n)$ the number of words of length $t$ over $H$ with profile $n$,
--   $$
--   \sum_{n}W_t(n)\prod_{h\in H}\pi(h)^{n(h)}=\Bigl(\sum_{h\in H}\pi(h)\Bigr)^t,
--   $$
--   the sum running over the attained profiles.
--
--   It is the multinomial theorem, with the multinomial coefficients defined as fibre counts. It normalizes the sum over profile groups.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingWords.lean#L69-L84

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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncoding
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWords

open OAI OAI.TalagrandThreshold
open scoped BigOperators
variable {H : Type*} [Fintype H] [DecidableEq H]

theorem OAI.TalagrandThreshold.sum_wordCount_weight (t : ℕ) (π : H → ℝ) :
    (∑ n ∈ wordProfiles H t, (wordCount t n : ℝ) * ∏ h, π h ^ n h) =
      (∑ h, π h) ^ t := by sorry
