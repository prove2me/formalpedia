-- Prove2me | Theorems.Thm_NagamochiIbaraki_EdgeConn_lemma_2_3
-- name    : NagamochiIbaraki.EdgeConn.lemma_2_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:02:26.119624+00:00
-- url     : https://prove2.me/theorems/54e2ce87-4557-419e-a039-a21cf3d97567
-- title:
--   Lemma 2.3 — every class E_i constructed by FOREST is a forest
-- statement:
--   Let $G = (V, E)$ be a finite multigraph without self-loops and with $|V| \ge 2$, and consider any execution of Procedure FOREST on $G$. At every time instant of the execution and for every $i = 1, 2, \dots, |E|$, the spanning subgraph
--
--   $$
--   F_i = (V, E_i)
--   $$
--
--   is a forest: it contains no cycle, where two parallel edges count as a cycle.
--
--   This is the first half of Lemma 2.5: the classes produced by FOREST are forests; Lemma 2.5 adds maximality.
--
--   **Formalization Note** "A forest" is expressed as "every edge of $E_i$ is a bridge of $E_i$", which sees parallel edges. The statement is made at every state $\sigma_k$, $k \le K$, of a run, which includes the final classes of a completed run ($k = K$).
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 587, Lemma 2.3

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

theorem lemma_2_3
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k ≤ K → ∀ i : ℕ, 1 ≤ i → i ≤ Fintype.card E →
      IsForest ends (cls (σ k) i) := by sorry

end NagamochiIbaraki.EdgeConn
