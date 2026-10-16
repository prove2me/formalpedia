-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_predecessor_conditional_ratio_le
-- name    : OAI.LeanBlast.SecondKahnKalai.predecessor_conditional_ratio_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:44:08.98335+00:00
-- url     : https://prove2.me/theorems/22286170-dac2-4639-b8df-a54e98201bc8
-- title:
--   Conditional containment ratios at a maximizing predecessor are at most $\sigma^{|J|}$
-- statement:
--   Let $G$ be a finite group acting on a set $X$. For a finite set $F\subseteq X$ and $g\in G$ write $gF=\{gx: x\in F\}$. The distinct sets of the form $gF$ are the *copies* of $F$; let $\mathcal{C}(F)=\{gF: g\in G\}$ be the set of copies (each set counted once, no matter how many group elements produce it). For finite $I,U\subseteq X$ let
--   $$
--   \pi_I(U)=\frac{\#\{J\in\mathcal{C}(I): U\subseteq J\}}{|\mathcal{C}(I)|}
--   $$
--   be the probability that a uniformly random copy of $I$ (uniform over the distinct copies) contains $U$. For $\sigma>0$ define the *score* $s_{I,\sigma}(S)=\pi_I(S)/\sigma^{|S|}$, and let $S^{*}=S^{*}(I,\sigma)$ be a fixed maximizer of $s_{I,\sigma}$ over all subsets $S\subseteq I$, the empty set included (the *maximizing predecessor* of $I$; if there are several maximizers, one of them is fixed once and for all).
--
--   **Theorem.** Let $I\subseteq X$ be finite and $\sigma>0$. For every copy $S_0\in\mathcal{C}(S^{*})$ of the maximizing predecessor and every finite set $J\subseteq X$ with $S_0\cap J=\emptyset$,
--   $$
--   \frac{\pi_I(S_0\cup J)}{\pi_I(S_0)}\le\sigma^{|J|}.
--   $$
--
--   The denominator is positive, because $S_0$ is a copy of a subset of $I$. Thus, conditionally on containing the copy $S_0$ of the predecessor, a uniformly random copy of $I$ contains any further set $J$ with probability at most $\sigma^{|J|}$: the newly added elements are $\sigma$-spread. This is the local spread property required at every level of the extension tree in the threshold argument, where it is used with $\sigma=128q$.
--
--   **Formalization Note** $\pi_I$ is `containmentProb G I`, the probability of the event under the uniform law on the orbit copies, and $S^{*}$ is `maximizingPredecessor G I σ`, a classical choice of maximizer over `I.powerset`. The set $J$ may be empty, in which case the ratio is $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/Predecessor.lean#L195-L210

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Action.Pointwise.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.List.Pairwise
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Monotone
import Definitions.Def_SecondKahnKalai
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphEncoding
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_EmbeddingExtension
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphSupport
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Basic
import Definitions.Def_OAI_Combinatorics_GraphThreshold_FiniteProbability
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CopyOrbits
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphExpectedCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphCopies
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTree
import Definitions.Def_OAI_Combinatorics_GraphThreshold_LocalFailureNumerics
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Predecessor

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
variable (G : Type*) [Group G] [Fintype G]
variable {X : Type*} [DecidableEq X] [MulAction G X]

theorem OAI.LeanBlast.SecondKahnKalai.predecessor_conditional_ratio_le (I : Finset X) {σ : ℝ} (hσ : 0 < σ)
    {S₀ J : Finset X}
    (hS₀ : S₀ ∈ copyOrbit G (maximizingPredecessor G I σ))
    (hdisj : Disjoint S₀ J) :
    containmentProb G I (S₀ ∪ J) / containmentProb G I S₀ ≤ σ ^ J.card := by sorry
