-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_sum_prod_wordCount_weight_le_one
-- name    : OAI.TalagrandThreshold.sum_prod_wordCount_weight_le_one
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:12:06.289847+00:00
-- url     : https://prove2.me/theorems/35b05345-f44f-4f03-bb86-341c026dc025
-- title:
--   Word-count weights sum to at most one over any set of profile tuples
-- statement:
--   Let $I$ and $H$ be finite, $t:I\to\mathbb{N}$, $E$ a finite set of tuples $(n_i)_{i\in I}$ of profiles $n_i:H\to\mathbb{N}$, and $\pi\ge0$ on $H$ with $\sum_h\pi(h)\le1$. Then
--   $$
--   \sum_{n\in E}\prod_{i\in I}W_{t_i}(n_i)\prod_h\pi(h)^{n_i(h)}\le1 .
--   $$
--
--   Summed over all profiles, the word factors of the group bound are probabilities of words. They can only lose mass when restricted to the profiles that occur.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingWordsProducts.lean#L45-L73

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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingWordsTransport
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingRows
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorProfile
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCountingEncodingBound
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorDelay
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorCommonWitness

open OAI OAI.TalagrandThreshold
open scoped BigOperators

theorem OAI.TalagrandThreshold.sum_prod_wordCount_weight_le_one {I H : Type*} [Fintype I]
    [Fintype H] [DecidableEq H] (t : I → ℕ) (E : Finset (I → H → ℕ))
    (π : H → ℝ) (hπ : ∀ h, 0 ≤ π h) (hπsum : (∑ h, π h) ≤ 1) :
    (∑ n ∈ E, ∏ i, ((wordCount (t i) (n i) : ℝ) * ∏ h, π h ^ (n i h))) ≤ 1 := by sorry
