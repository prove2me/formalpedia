-- Prove2me | Theorems.Thm_NagamochiIbaraki_NodeConn_lemma_2_2
-- name    : NagamochiIbaraki.NodeConn.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:08:22.981984+00:00
-- url     : https://prove2.me/theorems/2b162d45-a438-4c7c-8c39-982fb602cc3c
-- title:
--   Lemma 2.2 — during FOREST, a node v meets E_i exactly for i = 1, …, r(v)
-- statement:
--   Let $G = (V, E)$ be a graph with $|V| \ge 2$ and no self-loop (parallel edges allowed), and consider any run of Procedure FOREST on $G$. At every time instant of the run, for every node $v$ and every index $1 \le i \le |E|$, write $E(v)$ for the set of edges incident to $v$ and $E_i$ for the $i$-th class at that instant. Then
--
--   $$
--   E(v) \cap E_i \neq \emptyset \iff i \le r(v).
--   $$
--
--   Equivalently, $E(v) \cap E_i \ne \emptyset$ for $i = 1, \dots, r(v)$ and $E(v) \cap E_i = \emptyset$ for $i = r(v) + 1, \dots, |E|$: the label $r(v)$ counts exactly the classes that have already reached $v$.
--
--   This invariant is the basic bookkeeping fact about FOREST; it underlies the forest property of the classes, Lemma 2.4 and the Appendix proof of Lemma 3.1.
--
--   **Formalization Note** The paper states the lemma at the instants when the block of lines 7–10 has been completed for the current node; it is stated here at every state of the run, which is equivalent because the select and finish steps change neither the labels nor the classes.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 587, Lemma 2.2

import Mathlib
import Definitions.Def_NagamochiIbaraki_NodeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_NodeConn_Forest

namespace NagamochiIbaraki.NodeConn

theorem lemma_2_2
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (v : V) (i : ℕ), 1 ≤ i → i ≤ Fintype.card E →
      ((∃ e : E, v ∈ ends e ∧ (σ k).idx e = i) ↔ i ≤ (σ k).r v) := by sorry

end NagamochiIbaraki.NodeConn
