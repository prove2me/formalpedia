-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_ProbabilityTree_CoverState_exists_advance_of_good
-- name    : OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_good
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:15:07.125153+00:00
-- url     : https://prove2.me/theorems/8c859c5a-db80-457a-9597-3684119b0f57
-- title:
--   A good draw yields a strict advance of the cover state in the tree-covering iteration
-- statement:
--   Fix a ground set $X$, a probability tree $T_0$ on $X$ of some depth $k$ (the *original* tree), and a real number $\sigma$. The statement uses the following notions.
--
--   **Probability trees.** A probability tree of depth $0$ is a single leaf. A probability tree of depth $n+1$ consists of a root carrying a nonempty finite set $B$ of branches, a probability law $\mu$ on $B$ with $\mu(b)>0$ for every $b\in B$, a finite label $A_b\subseteq X$ on each branch $b$, and a probability tree $T_b$ of depth $n$ below each branch. The root is at level $0$, the roots of the subtrees $T_b$ are at level $1$, and so on. A *full path* $P$ is a sequence of branch choices from the root down to a leaf (different branch choices give different paths even when their labels agree), and $\bigcup P$ denotes the union of the labels along $P$. For a probability tree $T$:
--
--   - $T$ is *disjoint* if at every node each branch label $A_b$ is disjoint from all labels occurring in the subtree $T_b$;
--   - $T$ *has capacities* $c:\mathbb{N}\to\mathbb{N}$ if every branch leaving a node of level $i$ carries a label with at most $c(i)$ elements;
--   - $T$ *has spread* $\alpha:\mathbb{N}\to\mathbb{R}$ if at every node of level $i$, with law $\mu$ and labels $(A_b)_{b\in B}$, one has $\mu(\{b\in B: J\subseteq A_b\})\le\alpha(i)^{|J|}$ for every nonempty finite $J\subseteq X$;
--   - a probability tree $S$ of any depth *recovers* $T$ *modulo* a finite set $W\subseteq X$ if for every full path $Q$ of $S$ there is a full path $P$ of $T$ with $\bigcup P\subseteq W\cup\bigcup Q$.
--
--   **Cover states.** For $\ell\in\mathbb{N}$ put $r_\sigma(\ell)=4\sigma\prod_{j=1}^{\ell}(1-e^{-j})$ (the *reserve* at capacity $\ell$), and let $s(\ell)=\lfloor\log_2\ell\rfloor+1$ for $\ell\ge1$ and $s(0)=1$; for $\ell\ge1$, $s(\ell)$ is the number of halvings $\ell\mapsto\lfloor\ell/2\rfloor$ needed to reach $0$. A *cover state* for $(T_0,\sigma)$ is a quadruple $\Sigma=(d,S,c,Y)$ consisting of a depth $d\in\mathbb{N}$, a probability tree $S$ of depth $d$, a capacity sequence $c:\mathbb{N}\to\mathbb{N}$ and a finite set $Y\subseteq X$ of already seen elements, such that $S$ is disjoint, $S$ has capacities $c$, $S$ has spread $i\mapsto r_\sigma(c(i))$, $c(i)>0$ for all $i<d$, $16\,c(i)\le c(i+1)$ whenever $i+1<d$, and $S$ recovers $T_0$ modulo $Y$. Its *rank* is $\operatorname{rk}\Sigma=0$ if $d=0$ and $\operatorname{rk}\Sigma=s(c(d-1))$ if $d\ge1$. For a finite $W\subseteq X$, a cover state $\Sigma'=(d',S',c',Y')$ *advances* $\Sigma$ *on* $W$ if $\operatorname{rk}\Sigma'<\operatorname{rk}\Sigma$ and $Y'=Y\cup W$.
--
--   **Goodness.** Fix $\rho>0$ and a finite $W\subseteq X$. At a node with branch set $B$, law $\mu$ and labels $(A_b)_{b\in B}$, define for finite $F\subseteq X$ and $a,b\in B$
--
--   $$
--   N_F(b)=\begin{cases}\mu(b)\,\rho^{-|A_b|}&\text{if }A_b\subseteq F,\\ 0&\text{otherwise,}\end{cases}\qquad Z(F)=\sum_{b\in B}N_F(b),\qquad \pi_W(a,b)=\mu(a)\,\frac{N_{W\cup A_a}(b)}{Z(W\cup A_a)}.
--   $$
--
--   Thus $\pi_W$ is the law of a pair obtained by drawing a source branch $a$ from $\mu$ and then a target branch $b$ with probability proportional to $\mu(b)\rho^{-|A_b|}$ among the branches whose label lies inside $W\cup A_a$. For $\ell\in\mathbb{N}$, the pair $(a,b)$ is a *local success at capacity* $\ell$ if $Z(W\cup A_a)\ge e^{-10\ell}$ and $|A_b\setminus W|\le\lfloor\ell/2\rfloor$, and the *successful target mass* of $b$ is $w_\ell(b)=\sum_{a\in B}\pi_W(a,b)\,\mathbf{1}[(a,b)\text{ is a local success at capacity }\ell]$. For $c:\mathbb{N}\to\mathbb{N}$ write $c^{+}(i)=c(i+1)$. A leaf is $(\rho,c,W)$-good, and a tree with root data $(B,\mu,(A_b),(T_b))$ is $(\rho,c,W)$-good if
--
--   $$
--   \sum_{b\in B:\ T_b\text{ is }(\rho,c^{+},W)\text{-good}} w_{c(0)}(b)\ \ge\ 1-e^{-c(0)}.
--   $$
--
--   **Theorem.** Let $\sigma>0$ and $\rho>0$, let $\Sigma=(d,S,c,Y)$ be a cover state for $(T_0,\sigma)$ with $\operatorname{rk}\Sigma\neq0$, let $W\subseteq X$ be finite, and assume that the current tree $S$ is $(\rho,c,W)$-good, where $c$ is the capacity sequence of $\Sigma$. Then some cover state for $(T_0,\sigma)$ advances $\Sigma$ on $W$: there is a cover state $\Sigma'=(d',S',c',Y')$ for $(T_0,\sigma)$ with
--
--   $$
--   \operatorname{rk}\Sigma'<\operatorname{rk}\Sigma\qquad\text{and}\qquad Y'=Y\cup W.
--   $$
--
--   In the covering argument, $W$ is a $p$-random subset of a finite ground set and $\rho=p$. Goodness is a deterministic property of the pair $(S,W)$, evaluated on the current tree before any pruning or reweighting. A separate potential-function estimate shows that the current tree is good with probability at least $3/4$ when the reserve is small compared with $p$, and this theorem turns every good draw into an actual strict advance of the cover state; combined with an adaptive completion bound, this yields the probability estimate for covering a spread tree by a random set.
--
--   **Formalization Note** Goodness is `Good ρ state.capacity W state.tree`, defined by recursion on the tree; $N_F$, $Z$, $\pi_W$, local success and $w_\ell$ are `resamplingNumerator`, `resamplingZ`, `resamplingWeight`, `LocalSuccess` and `successfulTargetMass`, and $\rho^{-|A_b|}$ is written as a power of the inverse of $\rho$. Lean's convention that division by $0$ gives $0$ plays no role at the nodes of a probability tree, where $Z(W\cup A_a)\ge\mu(a)\rho^{-|A_a|}>0$. Cover states, rank, advancing, recovery, $r_\sigma$ and $s$ are `ProbabilityTree.CoverState original σ`, `CoverState.rank`, `CoverState.Advances`, `ProbabilityTree.Recovers`, `capacityReserve σ` and `successesNeeded` (the latter defined through `Nat.log2`); halving is natural-number division, and the ground type only needs decidable equality.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeCovering.lean#L330-L348

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai OAI.LeanBlast.SecondKahnKalai.ProbabilityTree OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState
open Classical
variable {X : Type} [DecidableEq X]
variable {k : ℕ} {original : ProbabilityTree X k} {σ : ℝ}

theorem OAI.LeanBlast.SecondKahnKalai.ProbabilityTree.CoverState.exists_advance_of_good (state : CoverState original σ) (W : Finset X)
    (hσ : 0 < σ) {ρ : ℝ} (hρ : 0 < ρ) (hrank : state.rank ≠ 0)
    (hgood : Good ρ state.capacity W state.tree) :
    ∃ next, state.Advances W next := by sorry
