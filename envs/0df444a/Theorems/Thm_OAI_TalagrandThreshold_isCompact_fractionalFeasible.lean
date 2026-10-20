-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_isCompact_fractionalFeasible
-- name    : OAI.TalagrandThreshold.isCompact_fractionalFeasible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:22:53.120385+00:00
-- url     : https://prove2.me/theorems/76b7b9d9-e2a1-471a-a72d-2aca4673c30b
-- title:
--   The set of fractionally feasible densities is compact
-- statement:
--   Let $X$ be a finite set and $\mathcal{F}$ a family of subsets of $X$. A family $\mathcal{G}$ covers $\mathcal{F}$ if every $H\in\mathcal{F}$ contains some $S\in\mathcal{G}$; its cost at density $p$ is $\sum_{S\in\mathcal{G}}p^{|S|}$, and $\mathcal{F}$ is $p$-small if some cover has cost at most $\frac12$. A fractional cover is a function $g$ on subsets of $X$ with values in $[0,1]$ such that $\sum_{S\subseteq H}g(S)\ge1$ for every $H\in\mathcal{F}$; its cost at density $r$ is $\sum_{S\subseteq X}g(S)r^{|S|}$. The set of fractionally feasible densities
--   $$
--   \Bigl\{p\in[0,1]:\ \exists\,g\text{ fractional cover of }\mathcal{F}\text{ with }\sum_Sg(S)p^{|S|}\le\tfrac12\Bigr\}
--   $$
--   is a compact subset of $\mathbb{R}$.
--
--   Consequently the fractional expectation threshold, its supremum, is attained whenever the set is nonempty. The rounding step can therefore be applied at $q_f(\mathcal{F})$ itself.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/ThresholdCompactness.lean#L32-L67

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
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_TupleCoefficients
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_SelectorGlobalCost
import Definitions.Def_OAI_Combinatorics_ExpectationThreshold_RoundingMain

open OAI OAI.TalagrandThreshold
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem OAI.TalagrandThreshold.isCompact_fractionalFeasible (F : Family α) :
    IsCompact (fractionalFeasible F) := by sorry
