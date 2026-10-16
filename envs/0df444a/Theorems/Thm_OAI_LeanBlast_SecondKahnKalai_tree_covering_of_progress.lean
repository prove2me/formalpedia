-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_tree_covering_of_progress
-- name    : OAI.LeanBlast.SecondKahnKalai.tree_covering_of_progress
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:16:01.729714+00:00
-- url     : https://prove2.me/theorems/29910444-e3c7-4644-9054-8118f451358c
-- title:
--   Covering a spread probability tree by a $p$-random set from a uniform progress estimate
-- statement:
--   Let $X$ be a finite set. For $p\in\mathbb{R}$ and a property $\mathcal P$ of subsets of $X$ put
--
--   $$
--   \mathbb P_p(\mathcal P)=\sum_{W\subseteq X:\ \mathcal P(W)}p^{|W|}(1-p)^{|X\setminus W|};
--   $$
--
--   for $0\le p\le1$ this is the probability that the $p$-random subset of $X$, which contains each element independently with probability $p$, has property $\mathcal P$. The statement uses the following notions.
--
--   **Probability trees.** A probability tree of depth $0$ is a single leaf. A probability tree of depth $n+1$ consists of a root carrying a nonempty finite set $B$ of branches, a probability law $\mu$ on $B$ with $\mu(b)>0$ for every $b\in B$, a finite label $A_b\subseteq X$ on each branch $b$, and a probability tree $T_b$ of depth $n$ below each branch. The root is at level $0$, the roots of the subtrees $T_b$ are at level $1$, and so on. A *full path* $P$ is a sequence of branch choices from the root down to a leaf (different branch choices give different paths even when their labels agree), and $\bigcup P$ denotes the union of the labels along $P$. For a probability tree $T$:
--
--   - $T$ is *disjoint* if at every node each branch label $A_b$ is disjoint from all labels occurring in the subtree $T_b$;
--   - $T$ *has capacities* $c:\mathbb{N}\to\mathbb{N}$ if every branch leaving a node of level $i$ carries a label with at most $c(i)$ elements;
--   - $T$ *has spread* $\alpha:\mathbb{N}\to\mathbb{R}$ if at every node of level $i$, with law $\mu$ and labels $(A_b)_{b\in B}$, one has $\mu(\{b\in B: J\subseteq A_b\})\le\alpha(i)^{|J|}$ for every nonempty finite $J\subseteq X$;
--   - a probability tree $S$ of any depth *recovers* $T$ *modulo* a finite set $W\subseteq X$ if for every full path $Q$ of $S$ there is a full path $P$ of $T$ with $\bigcup P\subseteq W\cup\bigcup Q$;
--   - $T$ is *covered by* a set $W\subseteq X$ if $\bigcup P\subseteq W$ for some full path $P$ of $T$.
--
--   **Cover states.** For $\ell\in\mathbb{N}$ put $r_\sigma(\ell)=4\sigma\prod_{j=1}^{\ell}(1-e^{-j})$ (the *reserve* at capacity $\ell$), and let $s(\ell)=\lfloor\log_2\ell\rfloor+1$ for $\ell\ge1$ and $s(0)=1$; for $\ell\ge1$, $s(\ell)$ is the number of halvings $\ell\mapsto\lfloor\ell/2\rfloor$ needed to reach $0$. A *cover state* for $(T,\sigma)$ is a quadruple $\Sigma=(d,S,c,Y)$ consisting of a depth $d\in\mathbb{N}$, a probability tree $S$ of depth $d$, a capacity sequence $c:\mathbb{N}\to\mathbb{N}$ and a finite set $Y\subseteq X$ of already seen elements, such that $S$ is disjoint, $S$ has capacities $c$, $S$ has spread $i\mapsto r_\sigma(c(i))$, $c(i)>0$ for all $i<d$, $16\,c(i)\le c(i+1)$ whenever $i+1<d$, and $S$ recovers $T$ modulo $Y$. Its *rank* is $\operatorname{rk}\Sigma=0$ if $d=0$ and $\operatorname{rk}\Sigma=s(c(d-1))$ if $d\ge1$. For a finite $W\subseteq X$, a cover state $\Sigma'=(d',S',c',Y')$ *advances* $\Sigma$ *on* $W$ if $\operatorname{rk}\Sigma'<\operatorname{rk}\Sigma$ and $Y'=Y\cup W$.
--
--   **Theorem.** Let $T$ be a probability tree on $X$ of depth $k\ge1$, let $m:\mathbb{N}\to\mathbb{N}$ and $\sigma\in\mathbb{R}$, and assume:
--
--   1. $T$ is disjoint and has capacities $m$;
--   2. $m(i)>0$ for all $i<k$, and $16\,m(i)\le m(i+1)$ whenever $i+1<k$;
--   3. $\sigma>0$, and $T$ has spread $\sigma$ at every level (spread sequence $i\mapsto\sigma$);
--   4. (progress) with $p_0=4e^{50}\sigma$: if $p_0<1$, then for every cover state $\Sigma$ for $(T,\sigma)$ with $\operatorname{rk}\Sigma\neq0$,
--      $$\mathbb P_{p_0}\bigl(W:\ \text{some cover state for }(T,\sigma)\text{ advances }\Sigma\text{ on }W\bigr)\ \ge\ \frac34 .$$
--
--   Then
--
--   $$
--   \mathbb P_{q}\bigl(T\text{ is covered by }W\bigr)\ \ge\ \frac23,\qquad\text{where}\quad q=\min\Bigl\{1,\ 16\,e^{50}\,\sigma\,\bigl(1+\log_2 m(k-1)\bigr)\Bigr\}.
--   $$
--
--   This statement isolates the probabilistic part of covering a spread tree by a random set: it converts a uniform lower bound on the chance that a single $p_0$-random draw lets any cover state of nonzero rank advance into a lower bound on the probability that a $q$-random set covers the whole tree, where $q$ is of order $\sigma\log_2 m(k-1)$. The progress hypothesis is supplied separately (a draw makes the current tree good with probability at least $3/4$, and good draws advance), and the resulting covering bound is the step that turns the expectation threshold of a graph into an upper bound on its critical threshold.
--
--   **Formalization Note** $\mathbb P_p$ is `bernoulliProbability p`, given by the product formula above for every real $p$; in hypothesis 4 the rate $p_0$ is positive and assumed below $1$, so it is a genuine probability there. $\log_2$ is `Real.logb 2`, and $m(k-1)$ uses natural-number subtraction with $k\ge1$. The tree is `T : ProbabilityTree X k`, covering is `T.CoveredBy`, constant spread is `T.HasSpread (fun _ => σ)`, cover states for $(T,\sigma)$ are `ProbabilityTree.CoverState T σ` with `rank` and `Advances` as described, $r_\sigma$ is `capacityReserve σ` and $s$ is `successesNeeded` (defined through `Nat.log2`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean#L354-L405

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
import Definitions.Def_OAI_Combinatorics_GraphThreshold_GraphHierarchy
import Definitions.Def_OAI_Combinatorics_GraphThreshold_BernoulliCoupling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_AdaptiveTrials
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeFacts
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ProbabilityTreeTrim
import Definitions.Def_OAI_Combinatorics_GraphThreshold_CapacityIteration
import Definitions.Def_OAI_Combinatorics_GraphThreshold_Resampling
import Definitions.Def_OAI_Combinatorics_GraphThreshold_ResamplingEvents
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReductionData
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeReduction
import Definitions.Def_OAI_Combinatorics_GraphThreshold_OutsideChangeOfMeasure
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreePotential
import Definitions.Def_OAI_Combinatorics_GraphThreshold_TreeCovering

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Classical

theorem OAI.LeanBlast.SecondKahnKalai.tree_covering_of_progress {X : Type} [Fintype X] [DecidableEq X]
    {k : ℕ} (T : ProbabilityTree X k) (hk : 0 < k) (hdis : T.IsDisjoint)
    (m : ℕ → ℕ) (hcap : T.HasCapacities m) (hpos : ∀ i, i < k → 0 < m i)
    (hgrowth : ∀ i, i + 1 < k → 16 * m i ≤ m (i + 1))
    (σ : ℝ) (hσ : 0 < σ) (hspread : T.HasSpread (fun _ => σ))
    (hprogress : Real.exp 50 * (4 * σ) < 1 →
      ∀ state : ProbabilityTree.CoverState T σ, state.rank ≠ 0 →
        (3 / 4 : ℝ) ≤ bernoulliProbability (Real.exp 50 * (4 * σ))
          (fun W => ∃ next, state.Advances W next)) :
    (2 / 3 : ℝ) ≤ bernoulliProbability
      (min 1 (16 * Real.exp 50 * σ * (1 + Real.logb 2 (m (k - 1) : ℝ)))) T.CoveredBy := by sorry
