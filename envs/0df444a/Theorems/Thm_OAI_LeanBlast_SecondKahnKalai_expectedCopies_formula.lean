-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_expectedCopies_formula
-- name    : OAI.LeanBlast.SecondKahnKalai.expectedCopies_formula
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:40:44.288628+00:00
-- url     : https://prove2.me/theorems/fd02c329-3b2d-42c7-8642-ae4777d70f83
-- title:
--   Expected number of copies of a graph $F$ in $G(n,p)$ equals $c(K_n,F)\,p^{e(F)}$
-- statement:
--   Let $n\in\mathbb{N}$ and $p\in\mathbb{R}$. Let $E_n$ be the set of unordered pairs $\{i,j\}$ of distinct elements of $\{0,\dots,n-1\}$ (the edges of the complete graph $K_n$), and for $W\subseteq E_n$ let $G_W$ be the graph on the vertex set $\{0,\dots,n-1\}$ whose edge set is $W$. Weight each $W\subseteq E_n$ by $w_p(W)=p^{|W|}(1-p)^{|E_n|-|W|}$; for $0\le p\le 1$ this is the law of the Erdős–Rényi random graph $G(n,p)$.
--
--   Let $F$ be a simple graph on a vertex set $V$. For a graph $\Gamma$ on $\{0,\dots,n-1\}$, a *copy* of $F$ in $\Gamma$ is a subgraph $K$ of $\Gamma$ (a set of vertices together with some of the $\Gamma$-edges joining them), regarded as a graph on its own vertex set, that is isomorphic to $F$; let $c(\Gamma,F)$ be the number of such subgraphs (unlabelled, not necessarily induced copies). Let $e(F)$ be the number of edges of $F$.
--
--   **Theorem.** For every $n\in\mathbb{N}$, every real $p$ and every graph $F$,
--   $$
--   \sum_{W\subseteq E_n}w_p(W)\,c(G_W,F)=c(K_n,F)\,p^{e(F)}.
--   $$
--
--   For $0\le p\le 1$ the left side is the expected number of copies of $F$ in $G(n,p)$, so the expectation equals the number of copies of $F$ in the complete graph times the probability $p^{e(F)}$ that all edges of one fixed copy are present. Because a copy is a subgraph with its own vertex set, isolated vertices of $F$ are accounted for in $c(K_n,F)$, while they do not affect $p^{e(F)}$. The formula makes the expectation threshold, which is defined through expected copy numbers of subgraphs, explicitly computable.
--
--   **Formalization Note** No assumption is made on $p$ or on the vertex type $V$. Here $e(F)$ is `edgeCount F`, i.e. `Nat.card` of the edge set (which would be $0$ for an infinite edge set); if $V$ is infinite, $F$ has no copy in $K_n$ and both sides are $0$. The left side is `expectedCopies n p F`, and $c(\Gamma,F)$ is Mathlib's `SimpleGraph.copyCount`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphExpectedCopies.lean#L106-L137

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
attribute [local instance] Classical.propDecidable
universe u
variable {n : ℕ} {V : Type u}

theorem OAI.LeanBlast.SecondKahnKalai.expectedCopies_formula (n : ℕ) (p : ℝ) (F : SimpleGraph V) :
    expectedCopies n p F =
      ((⊤ : SimpleGraph (Fin n)).copyCount F : ℝ) * p ^ edgeCount F := by sorry
