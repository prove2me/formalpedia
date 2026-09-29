-- Prove2me | Theorems.Thm_NagamochiIbaraki_EdgeConn_lemma_2_5
-- name    : NagamochiIbaraki.EdgeConn.lemma_2_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:04:23.834058+00:00
-- url     : https://prove2.me/theorems/d3edf75f-764e-4dfc-9497-959e11bf727a
-- title:
--   Lemma 2.5 — each (V, E_i) output by FOREST is a maximal spanning forest in G − E_1 ∪ ⋯ ∪ E_{i−1}
-- statement:
--   Let $G = (V, E)$ be a finite multigraph without self-loops and with $|V| \ge 2$, and let $E_1, E_2, \dots, E_{|E|}$ be the classes obtained by Procedure FOREST upon completion (for any choices at lines 5 and 6). Then for every $i = 1, 2, \dots, |E|$,
--
--   $$
--   (V, E_i) \text{ is a maximal spanning forest in } G - (E_1 \cup E_2 \cup \cdots \cup E_{i-1}),
--   $$
--
--   that is, $E_i$ is a forest contained in $E \setminus (E_1 \cup \dots \cup E_{i-1})$, and adding to it any other edge of that set creates a cycle. For $i = 1$ the removed union is empty and $E_1$ is a maximal spanning forest of $G$ itself.
--
--   Lemma 2.5 says that the single scan of FOREST produces exactly the sequence of forests required by Lemma 2.1; combined with Lemma 2.1 it gives inequality (2.1) for the output of FOREST.
--
--   **Formalization Note** The classes are those of the final state $\sigma_K$ of a completed run. The ground set $G - E_1 \cup \dots \cup E_{i-1}$ is written as the set of edges whose final index does not lie in $\{1, \dots, i-1\}$; at $i = 1$ this is all of $E$.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 588, Lemma 2.5

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

theorem lemma_2_5
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsCompletedRun ends σ K) :
    ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      IsMaxSpanningForest ends
        (Finset.univ.filter (fun e => ¬ (1 ≤ (σ K).idx e ∧ (σ K).idx e ≤ i - 1)))
        (cls (σ K) i) := by sorry

end NagamochiIbaraki.EdgeConn
