-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_orbitExtensionTree_support_disjoint
-- name    : OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_support_disjoint
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:46:58.743976+00:00
-- url     : https://prove2.me/theorems/08d12cca-0c82-484d-8382-39bfa6a14cae
-- title:
--   In an orbit extension tree the root copy is disjoint from the support below it
-- statement:
--   Let $G$ be a finite group acting on a set $X$. For a finite set $F\subseteq X$ and $g\in G$ write $gF=\{gx: x\in F\}$. The distinct sets of the form $gF$ are the *copies* of $F$; let $\mathcal{C}(F)=\{gF: g\in G\}$ be the set of copies (each set counted once, no matter how many group elements produce it).
--
--   A *probability tree* of depth $d$ on $X$ is a rooted tree all of whose root-to-leaf paths have length $d$, in which every internal node $v$ carries a finite set $B_v$ of children, a strictly positive probability distribution $\mu_v$ on $B_v$, and for each child $b\in B_v$ a finite *arc label* $L_v(b)\subseteq X$. The *support* $\operatorname{supp}(T)$ of a tree $T$ is the union of all arc labels occurring anywhere in $T$.
--
--   Fix $d\in\mathbb{N}$, finite sets $A_0,A_1,A_2,\ldots\subseteq X$ with $A_i\subseteq A_{i+1}$ for every $i<d$, and a copy $S_0\in\mathcal{C}(A_0)$. The *orbit extension tree* $T_d(A;S_0)$ is defined by recursion on $d$: $T_0(A;S_0)$ is a single leaf; for $d\ge 1$ the children of the root are the distinct copies $J\in\mathcal{C}(A_1)$ with $S_0\subseteq J$ (there is at least one, because $A_0\subseteq A_1$), with the uniform distribution; the arc to $J$ is labelled $J\setminus S_0$; and the subtree below $J$ is $T_{d-1}(A';J)$ for the shifted sequence $A'_i=A_{i+1}$. A root-to-leaf path thus corresponds to a chain of copies $S_0\subseteq J_1\subseteq\cdots\subseteq J_d$ with $J_i\in\mathcal{C}(A_i)$, each chosen uniformly among the copies of $A_i$ containing the previous one, and each arc records the newly added elements.
--
--   **Theorem.** Under these assumptions,
--   $$
--   S_0\cap\operatorname{supp}\bigl(T_d(A;S_0)\bigr)=\emptyset.
--   $$
--
--   In words, no element of the copy sitting at a node is ever added again further down the tree. This is the key step in showing that orbit extension trees are disjoint, i.e. that the arc labels along every root-to-leaf path are pairwise disjoint.
--
--   **Formalization Note** Trees are the inductive type `ProbabilityTree X d`. In `orbitExtensionTree G d A hnested S0 hS0` the children of a node are indexed by `ExtensionCopy G (A 1) S0`, the orbit copies of $A_1$ containing $S_0$, with the uniform law `extensionLaw`; the tree takes the nesting hypothesis and the membership $S_0\in\mathcal{C}(A_0)$ as arguments. The type $X$ (in the lowest universe) need not be finite. The support is `ProbabilityTree.support`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean#L171-L187

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

theorem OAI.LeanBlast.SecondKahnKalai.orbitExtensionTree_support_disjoint (d : ℕ) (A : ℕ → Finset X)
    (hnested : ∀ i, i < d → A i ⊆ A (i + 1))
    (S0 : Finset X) (hS0 : S0 ∈ copyOrbit G (A 0)) :
    Disjoint S0 (orbitExtensionTree G d A hnested S0 hS0).support := by sorry
