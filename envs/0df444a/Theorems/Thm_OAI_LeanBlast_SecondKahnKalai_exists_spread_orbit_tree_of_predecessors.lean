-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_exists_spread_orbit_tree_of_predecessors
-- name    : OAI.LeanBlast.SecondKahnKalai.exists_spread_orbit_tree_of_predecessors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:49:36.272968+00:00
-- url     : https://prove2.me/theorems/55dbccb9-33d5-4575-a58d-bafd6b16d388
-- title:
--   A spread tree whose paths are copies of $H$, built from a sparse predecessor rule
-- statement:
--   Let $G$ be a finite group acting on a set $X$. For a finite set $F\subseteq X$ and $g\in G$ write $gF=\{gx: x\in F\}$. The distinct sets of the form $gF$ are the *copies* of $F$; let $\mathcal{C}(F)=\{gF: g\in G\}$ be the set of copies (each set counted once, no matter how many group elements produce it). For finite $I,U\subseteq X$ let $\pi_I(U)$ be the probability that a uniformly random element of $\mathcal{C}(I)$ contains $U$.
--
--   A *probability tree* of depth $k$ on $X$ is a rooted tree whose root-to-leaf paths all have length $k$, where each internal node $v$ carries a finite set $B_v$ of children, a strictly positive probability distribution $\mu_v$ on $B_v$, and finite arc labels $L_v(b)\subseteq X$ for $b\in B_v$. Such a tree is *disjoint* if every arc label is disjoint from all labels in the subtree below that arc; it *has capacities* $m_0,m_1,\ldots$ if every label on an arc leaving a node at depth $i$ (the root has depth $0$) has at most $m_i$ elements; and it *has spread* $\sigma$ if $\mu_v(\{b: J\subseteq L_v(b)\})\le\sigma^{|J|}$ for every internal node $v$ and every nonempty finite $J\subseteq X$.
--
--   Let $H\subseteq X$ be a nonempty finite set, $\sigma\ge 0$, and $R$ a binary relation on finite subsets of $X$. Assume:
--
--   (P) every nonempty $I\subseteq H$ has some $S\subseteq I$ with $17|S|<|I|$ and $R(S,I)$;
--
--   (Q) whenever $I\subseteq H$, $R(S,I)$, $S_0\in\mathcal{C}(S)$, and $J\subseteq X$ is finite, nonempty and disjoint from $S_0$,
--   $$
--   \frac{\pi_I(S_0\cup J)}{\pi_I(S_0)}\le\sigma^{|J|}.
--   $$
--
--   **Theorem.** There exist $k\in\mathbb{N}$, natural numbers $m_0,m_1,\ldots$ and a probability tree $T$ of depth $k$ on $X$ such that
--
--   1. $k\ge 1$;
--   2. $T$ is disjoint;
--   3. $T$ has capacities $m_0,m_1,\ldots$;
--   4. $T$ has spread $\sigma$;
--   5. $m_i\ge 1$ for every $i<k$;
--   6. $16\,m_i\le m_{i+1}$ whenever $i+1<k$;
--   7. $m_{k-1}\le|H|$;
--   8. for every root-to-leaf path of $T$, the union of the arc labels along the path is a copy of $H$, i.e. belongs to $\mathcal{C}(H)$.
--
--   This assembles the spread-tree construction from an abstract predecessor rule: a random root-to-leaf path of $T$ samples a copy of $H$ in $k$ disjoint, geometrically growing, $\sigma$-spread pieces. In the graph-threshold application, $X$ is the edge set of $K_n$, $G$ is the symmetric group of the vertex set acting on edges, $R(S,I)$ says that $S$ is the maximizing predecessor of $I$ (a maximizer of $\pi_I(S)/\sigma^{|S|}$ over $S\subseteq I$), and $\sigma=128q$, where $q>0$ is such that every nonempty $U\subseteq H$ satisfies $\tfrac12\le|\mathcal{C}(U)|\,q^{|U|}$.
--
--   **Formalization Note** The tree is an element of `ProbabilityTree X k` (with `X : Type`); the properties are `IsDisjoint`, `HasCapacities m`, `HasSpread (fun _ => σ)`, and paths are the dependent type `T.Path` with label union `T.pathUnion p`, so different histories leading to equal sets are distinct paths. The capacities form a function $m:\mathbb{N}\to\mathbb{N}$, of which only $m_0,\dots,m_{k-1}$ matter. $X$ need not be finite.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphHierarchy.lean#L266-L300

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

theorem OAI.LeanBlast.SecondKahnKalai.exists_spread_orbit_tree_of_predecessors
    (H : Finset X) (hH : H.Nonempty) (σ : ℝ) (hσ : 0 ≤ σ)
    (R : Finset X → Finset X → Prop)
    (hpred : ∀ I, I ⊆ H → I.Nonempty →
      ∃ S, S ⊆ I ∧ 17 * S.card < I.card ∧ R S I)
    (hratio : ∀ I, I ⊆ H → ∀ S, R S I →
      ∀ S0 ∈ copyOrbit G S, ∀ J : Finset X, J.Nonempty → Disjoint S0 J →
        containmentProb G I (S0 ∪ J) / containmentProb G I S0 ≤ σ ^ J.card) :
    ∃ k : ℕ, ∃ m : ℕ → ℕ, ∃ T : ProbabilityTree X k,
      0 < k ∧ T.IsDisjoint ∧ T.HasCapacities m ∧ T.HasSpread (fun _ => σ) ∧
      (∀ i, i < k → 0 < m i) ∧
      (∀ i, i + 1 < k → 16 * m i ≤ m (i + 1)) ∧
      m (k - 1) ≤ H.card ∧
      ∀ p : T.Path, T.pathUnion p ∈ copyOrbit G H := by sorry
