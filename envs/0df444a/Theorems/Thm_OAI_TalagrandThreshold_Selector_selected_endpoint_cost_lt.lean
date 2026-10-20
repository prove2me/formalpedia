-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_selected_endpoint_cost_lt
-- name    : OAI.TalagrandThreshold.Selector.selected_endpoint_cost_lt
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:19:29.09113+00:00
-- url     : https://prove2.me/theorems/284c00cc-4f29-4e93-bf1d-c0c01150f869
-- title:
--   The selected originals of one endpoint cost less than $1/20$ of its mass
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring of a finite set $X$ is a map $a:X\to\{0,\dots,s\}$. For colorings $a,z$ with $z\le a$ pointwise, the changed set is $\{x:z(x)<a(x)\}$, and the profile $n_{a,z}(i,h)$ counts points with final color $i<s$ and original color $h>i$. Write $r_i(n)=\sum_hn(i,h)$ for the row counts. For $p>0$ with $p\Sigma_s\le\frac12$, where $\Sigma_s=\sum_{i<s}256^{\,i+1}$, colors have probabilities $\pi_c=256^{c+1}p$ for $c<s$ and $\pi_s=1-p\Sigma_s$, and a coloring $a$ has mass $\prod_{x}\pi_{a(x)}$. A mass family assigns to each member $H$ of a family $\mathcal{F}$ of subsets of $X$ a probability vector $\mu_H$ on $X$ supported in $H$. A coloring $a$ is bad if no member $H$ has $\mu_H(\{x:a(x)\le i\})\ge1-2^{-(i+1)}$ for all $i<s$. A coloring $z$ is a selected move of $a$ if, for some member $H_0$, it is a feasible earlier coloring of $a$ with changed set inside $H_0$ and of minimum movement $\sum_x(a(x)-z(x))$ among those. For a final coloring $z$, the selected originals are the bad $a$ having $z$ as a selected move, and the selected profiles are their profiles $n_{a,z}$. For every final coloring $z$,
--   $$
--   \sum_{a\text{ selected original of }z}\mathrm{mass}(a)\,p^{|\{x:z(x)<a(x)\}|}<\frac{\mathrm{mass}(z)}{20} .
--   $$
--
--   The weight of all bad colorings that move to $z$ is a small fraction of the mass of $z$. This is the local estimate behind the global cost bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorGlobalCost.lean#L98-L129

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

theorem OAI.TalagrandThreshold.Selector.selected_endpoint_cost_lt (mu : MassFamily F)
    (p : ℝ) (s : ℕ) (hp : 0 < p) (hs : p * scaleSum s ≤ 1 / 2)
    (z : Coloring α s) :
    (∑ a ∈ selectedOriginals mu z, colorMass p s a * p ^ (changes a z).card) <
      colorMass p s z * (1 / 20) := by sorry
