-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_orbitExtensionTree_hasSpread
-- name    : OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_hasSpread
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:48:20.399988+00:00
-- url     : https://prove2.me/theorems/908d2167-f626-4622-84c1-c06ac59e4842
-- title:
--   Orbit extension trees are $\sigma$-spread when conditional containment ratios are at most $\sigma^{|J|}$
-- statement:
--   Let $G$ be a finite group acting on a set $X$. For a finite set $F\subseteq X$ and $g\in G$ write $gF=\{gx: x\in F\}$. The distinct sets of the form $gF$ are the *copies* of $F$; let $\mathcal{C}(F)=\{gF: g\in G\}$ be the set of copies (each set counted once, no matter how many group elements produce it). For finite $I,U\subseteq X$ let
--   $$
--   \pi_I(U)=\frac{\#\{J\in\mathcal{C}(I): U\subseteq J\}}{|\mathcal{C}(I)|}
--   $$
--   be the probability that a uniformly random copy of $I$ (uniform over the distinct copies) contains $U$.
--
--   A *probability tree* of depth $d$ on $X$ is a rooted tree all of whose root-to-leaf paths have length $d$, in which every internal node $v$ carries a finite set $B_v$ of children, a strictly positive probability distribution $\mu_v$ on $B_v$, and for each child $b\in B_v$ a finite *arc label* $L_v(b)\subseteq X$. The *support* $\operatorname{supp}(T)$ of a tree $T$ is the union of all arc labels occurring anywhere in $T$.
--
--   Fix $d\in\mathbb{N}$, finite sets $A_0,A_1,A_2,\ldots\subseteq X$ with $A_i\subseteq A_{i+1}$ for every $i<d$, and a copy $S_0\in\mathcal{C}(A_0)$. The *orbit extension tree* $T_d(A;S_0)$ is defined by recursion on $d$: $T_0(A;S_0)$ is a single leaf; for $d\ge 1$ the children of the root are the distinct copies $J\in\mathcal{C}(A_1)$ with $S_0\subseteq J$ (there is at least one, because $A_0\subseteq A_1$), with the uniform distribution; the arc to $J$ is labelled $J\setminus S_0$; and the subtree below $J$ is $T_{d-1}(A';J)$ for the shifted sequence $A'_i=A_{i+1}$. A root-to-leaf path thus corresponds to a chain of copies $S_0\subseteq J_1\subseteq\cdots\subseteq J_d$ with $J_i\in\mathcal{C}(A_i)$, each chosen uniformly among the copies of $A_i$ containing the previous one, and each arc records the newly added elements.
--
--   A probability tree *has spread* $\sigma$ if for every internal node $v$ and every nonempty finite $J\subseteq X$,
--   $\mu_v(\{b\in B_v: J\subseteq L_v(b)\})\le\sigma^{|J|}$.
--
--   **Theorem.** Let $\sigma\ge 0$, and let $A$ be nested as above. Assume that for every $i<d$, every copy $S\in\mathcal{C}(A_i)$ and every nonempty finite $J\subseteq X$ with $S\cap J=\emptyset$,
--   $$
--   \frac{\pi_{A_{i+1}}(S\cup J)}{\pi_{A_{i+1}}(S)}\le\sigma^{|J|}.
--   $$
--   Then for every copy $S_0\in\mathcal{C}(A_0)$ the tree $T_d(A;S_0)$ has spread $\sigma$.
--
--   The hypothesis bounds conditional containment probabilities for uniformly random copies (the denominators are positive, since $S$ is a copy of $A_i\subseteq A_{i+1}$); the conclusion is the spread condition at every node, which is what the spread-tree machinery of the threshold argument consumes. Because the hypothesis is quantified over all copies of $A_i$, it applies at every node of depth $i$, whatever history leads to it.
--
--   **Formalization Note** Trees are the inductive type `ProbabilityTree X d`. In `orbitExtensionTree G d A hnested S0 hS0` the children of a node are indexed by `ExtensionCopy G (A 1) S0`, the orbit copies of $A_1$ containing $S_0$, with the uniform law `extensionLaw`; the tree takes the nesting hypothesis and the membership $S_0\in\mathcal{C}(A_0)$ as arguments. The type $X$ (in the lowest universe) need not be finite. The conclusion is `HasSpread (fun _ => σ)`, i.e. the condition `IsSpread` with the same parameter $\sigma$ at every level, and $\pi_I$ is `containmentProb G I`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean#L243-L264

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open Finset
variable (G : Type*) [Group G] [Fintype G]
variable {X : Type} [DecidableEq X] [MulAction G X]

theorem OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_hasSpread (σ : ℝ) (hσ : 0 ≤ σ)
    (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (hratio : ∀ i, i < d → ∀ S0 ∈ copyOrbit G (A i),
      ∀ J : Finset X, J.Nonempty → Disjoint S0 J →
        containmentProb G (A (i + 1)) (S0 ∪ J) /
          containmentProb G (A (i + 1)) S0 ≤ σ ^ J.card)
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0)) :
    (orbitExtensionTree G d A hnested S0 hS0).HasSpread (fun _ => σ) := by sorry
