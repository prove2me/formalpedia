-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_sum_profile_weights_lt_one_twentieth
-- name    : OAI.TalagrandThreshold.Selector.sum_profile_weights_lt_one_twentieth
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T13:16:53.352608+00:00
-- url     : https://prove2.me/theorems/164cb247-087b-49b4-8595-b38c58862d4e
-- title:
--   The profile weights of nonzero row counts sum to less than $1/20$
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring of a finite set $X$ is a map $a:X\to\{0,\dots,s\}$. For colorings $a,z$ with $z\le a$ pointwise, the changed set is $\{x:z(x)<a(x)\}$, and the profile $n_{a,z}(i,h)$ counts points with final color $i<s$ and original color $h>i$. Write $r_i(n)=\sum_hn(i,h)$ for the row counts. For $p>0$ with $p\Sigma_s\le\frac12$, where $\Sigma_s=\sum_{i<s}256^{\,i+1}$, colors have probabilities $\pi_c=256^{c+1}p$ for $c<s$ and $\pi_s=1-p\Sigma_s$, and a coloring $a$ has mass $\prod_{x}\pi_{a(x)}$. Let $W_t(m)$ be the number of words of length $t$ over the colors whose letter counts are $m$. For every finite set $N$ of profiles whose row-count vectors $(r_i(n))_{i<s}$ are nonzero,
--   $$
--   \sum_{n\in N}\ \prod_{i<s}\Bigl(\frac{3}{64^{\,i+1}}\Bigr)^{r_i(n)}\ \prod_{i<s}W_{r_i(n)}\bigl(n(i,\cdot)\bigr)\prod_h\pi_h^{\,n(i,h)}<\frac1{20} .
--   $$
--
--   This is the budget of the selector, summed over the profiles that occur for one endpoint. No independence between the rows of the family $N$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorGlobalCostProfiles.lean#L20-L69

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

open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators

theorem OAI.TalagrandThreshold.Selector.sum_profile_weights_lt_one_twentieth (p : ℝ) (s : ℕ) (hp : 0 < p)
    (hs : p * scaleSum s ≤ 1 / 2) (N : Finset (Profile s))
    (hN : ∀ n ∈ N, rowCount n ≠ 0) :
    (∑ n ∈ N,
      (∏ i : Fin s, ((3 : ℝ) / 64 ^ (i.val + 1)) ^ (rowCount n i)) *
      (∏ i : Fin s, ((wordCount (rowCount n i) (n i) : ℝ) *
        ∏ h : Color s, colorProb p s h ^ (n i h)))) < 1 / 20 := by sorry
