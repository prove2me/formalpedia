-- Prove2me | Theorems.Thm_OAI_LeanBlast_SecondKahnKalai_isContained_iff_exists_smul_subset
-- name    : OAI.LeanBlast.SecondKahnKalai.isContained_iff_exists_smul_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T01:39:08.167052+00:00
-- url     : https://prove2.me/theorems/cf8315f6-90f6-4aa5-8c93-96542c6a3f79
-- title:
--   A graph on $[n]$ contains a copy of $H$ iff its edge set contains a permuted copy of a fixed embedding of $H$
-- statement:
--   Let $n$ be a natural number, $[n]=\{0,1,\dots,n-1\}$, and let $\mathcal E_n$ be the set of unordered pairs $\{i,j\}$ of distinct elements of $[n]$ (the edges of the complete graph $K_n$). For a finite set $S\subseteq\mathcal E_n$, write $G_S$ for the simple graph on $[n]$ whose edge set is $S$, and for a simple graph $G$ on $[n]$ write $E(G)\subseteq\mathcal E_n$ for its edge set. A permutation $\sigma$ of $[n]$ acts on edges by $\sigma\cdot\{i,j\}=\{\sigma(i),\sigma(j)\}$ and on sets of edges elementwise.
--
--   Let $V$ be a set, $H$ a simple graph on $V$, and $f:V\to[n]$ an injective map; $f(H)$ denotes the image graph on $[n]$, whose edges are the pairs $\{f(u),f(v)\}$ with $uv$ an edge of $H$. Say that $H$ is *contained* in a graph $G$, written $H\sqsubseteq G$, if there is an injective map from the vertices of $H$ to the vertices of $G$ that sends edges to edges (a non-induced copy of $H$ in $G$). Then for every finite set $W\subseteq\mathcal E_n$,
--   $$H\sqsubseteq G_W\iff\exists\,\sigma\in\mathfrak S_n:\quad \sigma\cdot E\big(f(H)\big)\subseteq W .$$
--
--   In words, $G_W$ contains a copy of $H$ exactly when $W$ contains one of the edge sets in the orbit of the fixed edge set $E(f(H))$ under the symmetric group $\mathfrak S_n$. Since copies are injective on all of $V$, isolated vertices of $H$ are taken into account. The equivalence turns the event that a random graph on $[n]$ contains a copy of $H$ into the event that a random edge set covers some member of a permutation orbit of a fixed edge set, which is the form used in the threshold arguments of this development.
--
--   **Formalization Note** $[n]$ is `Fin n`, $\mathcal E_n$ is the subtype `Edge n` of non-diagonal elements of `Sym2 (Fin n)`, $G_S$ is `graphOfEdges S`, $E(G)$ is `graphEdges G`, the injection is an embedding `f : V ↪ Fin n`, containment is Mathlib's `SimpleGraph.IsContained`, and `Equiv.Perm (Fin n)` acts on finite sets of edges pointwise. No finiteness of $V$ is assumed beyond what the injection into $[n]$ implies.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/GraphThreshold/GraphContainment.lean#L26-L49

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

open OAI OAI.LeanBlast OAI.LeanBlast.SecondKahnKalai
open scoped Pointwise
variable {n : ℕ} {V : Type*}

theorem OAI.LeanBlast.SecondKahnKalai.isContained_iff_exists_smul_subset (f : V ↪ Fin n) (H : SimpleGraph V)
    (W : Finset (Edge n)) :
    H.IsContained (graphOfEdges W) ↔
      ∃ σ : Equiv.Perm (Fin n), σ • graphEdges (H.map f) ⊆ W := by sorry
