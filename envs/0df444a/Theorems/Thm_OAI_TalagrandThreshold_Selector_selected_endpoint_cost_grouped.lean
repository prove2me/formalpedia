-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_selected_endpoint_cost_grouped
-- name    : OAI.TalagrandThreshold.Selector.selected_endpoint_cost_grouped
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:17:29.062244+00:00
-- url     : https://prove2.me/theorems/3e2d950f-a11c-47cd-a8a2-55aacc2306d7
-- title:
--   Selected originals of an endpoint split by their profile
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring of a finite set $X$ is a map $a:X\to\{0,\dots,s\}$. For colorings $a,z$ with $z\le a$ pointwise, the changed set is $\{x:z(x)<a(x)\}$, and the profile $n_{a,z}(i,h)$ counts points with final color $i<s$ and original color $h>i$. Write $r_i(n)=\sum_hn(i,h)$ for the row counts. A mass family assigns to each member $H$ of a family $\mathcal{F}$ of subsets of $X$ a probability vector $\mu_H$ on $X$ supported in $H$. A coloring $a$ is bad if no member $H$ has $\mu_H(\{x:a(x)\le i\})\ge1-2^{-(i+1)}$ for all $i<s$. A coloring $z$ is a selected move of $a$ if, for some member $H_0$, it is a feasible earlier coloring of $a$ with changed set inside $H_0$ and of minimum movement $\sum_x(a(x)-z(x))$ among those. For a final coloring $z$, the selected originals are the bad $a$ having $z$ as a selected move, and the selected profiles are their profiles $n_{a,z}$. For every final coloring $z$ and every $f$ on colorings,
--   $$
--   \sum_{a\text{ selected original of }z}f(a)=\sum_{n\text{ selected profile of }z}\ \ \sum_{a\in\text{group}(z,n)}f(a),
--   $$
--   where $\text{group}(z,n)$ is the set of selected originals $a$ with $n_{a,z}=n$.
--
--   Grouping by the profile that actually occurs loses no original coloring. Each group can then be bounded separately.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorGlobalCost.lean#L57-L76

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

open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators Classical
variable {α : Type*} [Fintype α] [DecidableEq α]
variable {F : Family α} {s : ℕ}

theorem OAI.TalagrandThreshold.Selector.selected_endpoint_cost_grouped (mu : MassFamily F)
    (z : Coloring α s) (f : Coloring α s → ℝ) :
    (∑ a ∈ selectedOriginals mu z, f a) =
      ∑ n ∈ selectedProfiles mu z, ∑ a ∈ groupOriginals mu z n, f a := by sorry
