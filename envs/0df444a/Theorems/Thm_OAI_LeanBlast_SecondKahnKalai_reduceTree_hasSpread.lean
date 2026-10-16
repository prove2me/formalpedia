-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_reduceTree_hasSpread
-- name    : OAI.LeanBlast.SecondKahnKalai.reduceTree_hasSpread
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T02:02:05.975604+00:00
-- url     : https://prove2.me/theorems/c9c3ad65-501f-457a-ad47-f7cd073c499e
-- title:
--   Tree reduction inflates each level's spread parameter by at most the factor $1/(1-e^{-m_j})$
-- statement:
--   **Probability trees.** Let $X$ be a set. A *probability tree* of depth $d\in\mathbb{N}$ over $X$ is defined recursively: the tree of depth $0$ is a single leaf, and a tree of depth $d+1$ is a node $T=(B,\mu,A,(T_b)_{b\in B})$ consisting of a finite index set $B$, a probability law $\mu$ on $B$ with $\mu(b)>0$ for every $b$, a finite label $A_b\subseteq X$ for every $b\in B$, and a child tree $T_b$ of depth $d$ for every $b\in B$. For a finite index set $B$ with a law $\mu$ and labels $(A_b)$, and a real $a$, the pair $(\mu,A)$ is *$a$-spread* if
--   $\mu(\{b: J\subseteq A_b\})\le a^{|J|}$ for every nonempty finite $J\subseteq X$. A tree has *spread profile* $a=(a_0,a_1,\dots)$ if at its root $(\mu,A)$ is $a_0$-spread and every child $T_b$ has spread profile $(a_1,a_2,\dots)$ (every profile is accepted by a leaf).
--
--   **Resampling quantities.** Let $B$ be a finite index set with a probability law $\mu$ (weights $\mu(b)\ge0$, $\sum_b\mu(b)=1$), let $A=(A_b)_{b\in B}$ be finite labels $A_b\subseteq X$, let $\rho>0$, let $W\subseteq X$ be finite and let $M\in\mathbb{N}$. Put
--   $$
--   Z(Y)=\sum_{b\in B:\ A_b\subseteq Y}\mu(b)\,\rho^{-|A_b|},\qquad
--   \pi(c,b)=\mu(c)\cdot\frac{\mathbf 1[A_b\subseteq W\cup A_c]\;\mu(b)\,\rho^{-|A_b|}}{Z(W\cup A_c)}\qquad(c,b\in B).
--   $$
--   So $\pi$ describes a *source* $c$ drawn from $\mu$ followed by a *target* $b$ chosen among the indices whose label lies in $W\cup A_c$, with probability proportional to $\mu(b)\rho^{-|A_b|}$. A pair $(c,b)$ is a *local success* $S_M(c,b)$ if $Z(W\cup A_c)\ge e^{-10M}$ and $|A_b\setminus W|\le\lfloor M/2\rfloor$, and a *local failure* otherwise. The *successful target mass* of $b$ is $s_M(b)=\sum_{c\in B:\ S_M(c,b)}\pi(c,b)$.
--
--   **Good trees and the reduced tree.** For a sequence of capacities $m=(m_0,m_1,\dots)$ of natural numbers write $m^{+}=(m_1,m_2,\dots)$, and fix $\rho>0$ and a finite set $W\subseteq X$. A leaf is *good*; a node $T=(B,\mu,A,(T_b))$ is *good* for $(\rho,m,W)$ if
--   $$
--   \sum_{b\in B:\ T_b\text{ is good for }(\rho,m^{+},W)} s_{m_0}(b)\ \ge\ 1-e^{-m_0},
--   $$
--   where $s_{m_0}$ is computed at this node from $(\mu,A,\rho,W)$. If $m_j>0$ for all $j<d$ and $T$ is good, the *reduced tree* $R(T)=R_{\rho,m,W}(T)$, again of depth $d$, is defined recursively: $R(\text{leaf})=\text{leaf}$, and for a node, $R(T)$ is the node with index set $B'=\{b\in B: T_b\text{ is good for }(\rho,m^{+},W)\text{ and }s_{m_0}(b)>0\}$, law $\mu'(b)=s_{m_0}(b)\big/\sum_{b''\in B'}s_{m_0}(b'')$, labels $A'_b=A_b\setminus W$, and children $R_{\rho,m^{+},W}(T_b)$ for $b\in B'$. (Goodness and $m_0>0$ make the normalizing sum at least $1-e^{-m_0}>0$.)
--
--   **Theorem.** Let $\rho>0$, let $m$ be capacities with $m_j>0$ for all $j<d$, let $W\subseteq X$ be finite, and let $T$ be a probability tree of depth $d$ that is good for $(\rho,m,W)$. Let $a=(a_0,a_1,\dots)$ be real numbers with $a_j\ge0$ for $j<d$ such that $T$ has spread profile $a$. Then $R_{\rho,m,W}(T)$ has spread profile $a'$, where
--   $$
--   a'_j=\frac{a_j}{1-e^{-m_j}}\qquad(j\in\mathbb{N}).
--   $$
--
--   Reduction keeps, at every good node, at least a $(1-e^{-m_0})$-fraction of the mass, and the theorem shows that this pruning and renormalization, together with the replacement of labels by their parts outside $W$, worsens the spread parameter of each level only by the reciprocal of that fraction. This controlled loss is what allows the reduction to be iterated while the capacities shrink.
--
--   **Formalization Note** Probability trees are the inductive type `ProbabilityTree X d` (constructors `leaf` and `node`), goodness is `Good ρ m W T`, and the reduced tree is `reduceTree ρ m W T hρ hm hg`, which takes the proofs of $\rho>0$, of $m_j>0$ for $j<d$ and of goodness as arguments; its index set at a node is the subtype `RetainedIndex` of indices that have a good child and positive successful target mass. Capacities form a function `m : ℕ → ℕ`, $\lfloor M/2\rfloor$ is natural-number division, and $X$ is a type with decidable equality. The spread profile is `ProbabilityTree.HasSpread` with `a : ℕ → ℝ`, built from `IsSpread μ A a`, which quantifies over nonempty `J : Finset X`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/TreeReduction.lean#L249-L281

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped BigOperators
open Classical
variable {X : Type} [DecidableEq X]

theorem OAI.LeanBlast.SecondKahnKalai.reduceTree_hasSpread (ρ : ℝ) (m : ℕ → ℕ) (W : Finset X) {d : ℕ}
    (T : ProbabilityTree X d) (hρ : 0 < ρ) (hm : ∀ j < d, 0 < m j)
    (hg : Good ρ m W T) (a : ℕ → ℝ) (ha : ∀ j < d, 0 ≤ a j)
    (hT : T.HasSpread a) :
    (reduceTree ρ m W T hρ hm hg).HasSpread
      (fun j => a j / (1 - Real.exp (-(m j : ℝ)))) := by sorry
