-- Prove2me | Theorems.Thm_OAI_TalagrandThreshold_Selector_card_le_profile_encoding
-- name    : OAI.TalagrandThreshold.Selector.card_le_profile_encoding
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:55:46.349869+00:00
-- url     : https://prove2.me/theorems/8a87ed20-75c5-43bb-bc73-281eef6cef85
-- title:
--   A profile group is no larger than its row-encoding count
-- statement:
--   Fix $s\in\mathbb{N}$. Colors are $0,\dots,s$ and a coloring of a finite set $X$ is a map $a:X\to\{0,\dots,s\}$. For $i<s$, $P_i(z)=\{x:z(x)\le i\}$, $d_i=2^{-(i+1)}$, the crossings are $|P_i(z)\setminus P_i(a)|$, the moved row $i$ is $\{x:z(x)=i<a(x)\}$, and the movement is $\sum_x(a(x)-z(x))$. The profile $n_{a,z}(i,h)$ counts points with final color $i$ and original color $h>i$. Let $G$ be a finite set of colorings, $z$ a coloring, $n$ a profile and $R_0,\dots,R_{s-1}\subseteq X$. Assume every $a\in G$ satisfies $z\le a$, $n_{a,z}=n$, and the moved row $i$ of $a$ lies in $R_i$ for each $i$. Then
--   $$
--   |G|\le\prod_{i<s}\binom{|R_i|}{r_i}\,W_{r_i}\bigl(n(i,\cdot)\bigr),\qquad r_i=\sum_hn(i,h).
--   $$
--
--   When the $R_i$ are small heavy sets, this bounds the number of bad colorings that select $z$ with profile $n$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/ExpectationThreshold/SelectorCountingEncodingBound.lean#L66-L89

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

open OAI OAI.TalagrandThreshold OAI.TalagrandThreshold.Selector
open scoped BigOperators
variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

theorem OAI.TalagrandThreshold.Selector.card_le_profile_encoding
    (G : Finset (Coloring α s)) (z : Coloring α s) (n : Profile s)
    (R : Fin s → Finset α)
    (hEarlier : ∀ a ∈ G, Earlier a z)
    (hprofile : ∀ a ∈ G, profile a z = n)
    (hrows : ∀ a ∈ G, ∀ i, movedRow a z i ⊆ R i) :
    G.card ≤ ∏ i : Fin s,
      Nat.choose (R i).card (rowCount n i) * wordCount (rowCount n i) (n i) := by sorry
