-- Prove2me | Theorems.Thm_NashWilliams61_TreePacking_lemma_6
-- name    : NashWilliams61.TreePacking.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:27:53.850653+00:00
-- url     : https://prove2.me/theorems/e015c2a1-6ab2-4f84-b8d7-be9ab5a1185b
-- title:
--   Lemma 6 — a non-trivial critical partition yields $k$ edge-disjoint spanning trees (inductive step)
-- statement:
--   Let $G$ be a finite multigraph without loops on vertex set $V$ with edge set $E$, and $k \ge 1$. Assume the standing hypotheses of the paper's proof of sufficiency:
--
--   1. $G$ is admissible;
--   2. $|V| \ge 2$;
--   3. (inductive hypothesis) every finite loopless multigraph $\tilde G$ with a non-empty vertex set, $|V(\tilde G)| + |E(\tilde G)| < |V| + |E|$, which is admissible, has $k$ edge-disjoint spanning trees.
--
--   If $V$ has a critical partition $P$, i.e. $|E_P(G)| = k(|P| - 1)$, which is neither the one-part partition $\{V\}$ nor the partition of $V$ into singletons, then $G$ has $k$ edge-disjoint spanning trees.
--
--   This disposes of the case of a non-trivial critical partition in the induction proving Theorem 1, by applying the inductive hypothesis to the subgraphs $X^*$ on the members of $P$ and to the shrunk graph $G_P$.
--
--   **Formalization Note** The paper's "inductive hypothesis that Theorem 1 is true for graphs $\tilde G$ such that $|V(\tilde G) \cup E(\tilde G)| < |V(G) \cup E(G)|$" is stated explicitly as hypothesis 3, with $|V(\tilde G) \cup E(\tilde G)|$ read as $|V(\tilde G)| + |E(\tilde G)|$ and with the direction of Theorem 1 that the proof uses (admissible implies $k$ trees; the converse is proved unconditionally as necessity). The smaller graphs range over arbitrary finite vertex and edge types. "Neither $\{V(G)\}$ nor the partition into subsets of order 1" is stated as: the parts of $P$ are not $\{V\}$, and not every part has exactly one element.
-- source:
--   Nash-Williams, Edge-disjoint spanning trees of finite graphs, J. London Math. Soc. 36 (1961), p. 448, Lemma 6 (with the standing assumptions of the proof of sufficiency stated just before it)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NashWilliams61_TreePacking_Graphs
open NagamochiIbaraki.EdgeConn

namespace NashWilliams61.TreePacking

/-- **Lemma 6** (Nash-Williams 1961, p. 448), under the standing assumptions of the proof of
sufficiency: `G` is admissible, `|V(G)| ≥ 2`, and (inductive hypothesis) every admissible
loopless multigraph `G̃` with `|V(G̃)| + |E(G̃)| < |V(G)| + |E(G)|` has `k` edge-disjoint
spanning trees. If `V(G)` has a critical partition `P` which is neither `{V(G)}` nor the
partition of `V(G)` into subsets of order `1`, `G` has `k` edge-disjoint spanning trees. -/
theorem lemma_6 {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag) (k : ℕ) (hk : 0 < k)
    (hadm : IsAdmissible k ends) (hV : 2 ≤ Fintype.card V)
    (IH : ∀ (V' E' : Type) [Fintype V'] [DecidableEq V'] [Nonempty V'] [Fintype E']
      [DecidableEq E'] (ends' : E' → Sym2 V'), (∀ e, ¬ (ends' e).IsDiag) →
      Fintype.card V' + Fintype.card E' < Fintype.card V + Fintype.card E →
      IsAdmissible k ends' → HasKTrees k ends')
    (P : Finpartition (Finset.univ : Finset V)) (hP : IsCriticalPartition k ends P)
    (hP1 : P.parts ≠ {Finset.univ}) (hP2 : ¬ ∀ X ∈ P.parts, X.card = 1) :
    HasKTrees k ends := by sorry

end NashWilliams61.TreePacking
