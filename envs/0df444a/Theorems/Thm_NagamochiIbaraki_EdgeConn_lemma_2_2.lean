-- Prove2me | Theorems.Thm_NagamochiIbaraki_EdgeConn_lemma_2_2
-- name    : NagamochiIbaraki.EdgeConn.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:01:57.537868+00:00
-- url     : https://prove2.me/theorems/e2aa8b5f-81a1-41b1-b62d-1dc462d0736c
-- title:
--   Lemma 2.2 — during FOREST, node v meets exactly the classes E_1, …, E_{r(v)}
-- statement:
--   Let $G = (V, E)$ be a finite multigraph without self-loops and with $|V| \ge 2$, and consider any execution of Procedure FOREST on $G$, with any choices at lines 5 and 6. Let $E(v)$ denote the set of edges incident to a node $v$, and let $E_i$ and $r(v)$ denote the classes and labels held by FOREST at some time instant of the execution. Then, for every node $v$,
--
--   $$
--   E(v) \cap E_i \ne \emptyset \quad (i = 1, 2, \dots, r(v)), \qquad E(v) \cap E_i = \emptyset \quad (i = r(v) + 1, \dots, |E|).
--   $$
--
--   In words, the label $r(v)$ counts the classes that already contain an edge at $v$, and these are the first $r(v)$ classes. This invariant is what makes the rule of line 7 put an edge $(x, y)$ into the first class that does not yet meet $y$; it underlies the forest property (Lemma 2.3) and the path property (Lemma 2.4).
--
--   **Formalization Note** The paper states the invariant at the instants when the block of lines 7–10 has just been completed. Here it is stated at every state $\sigma_k$, $k \le K$, of a run $\sigma_0, \dots, \sigma_K$; the other steps (select, finish) change neither the labels nor the classes, so this is the same assertion at more instants. The statement is the equivalence "some edge at $v$ lies in $E_i$ iff $i \le r(v)$" for $1 \le i \le |E|$.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 587, Lemma 2.2

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

theorem lemma_2_2
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ (v : V) (i : ℕ), 1 ≤ i → i ≤ Fintype.card E →
      ((∃ e : E, v ∈ ends e ∧ (σ k).idx e = i) ↔ i ≤ (σ k).r v) := by sorry

end NagamochiIbaraki.EdgeConn
