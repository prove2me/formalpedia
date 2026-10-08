-- Prove2me | Theorems.Thm_NagamochiIbaraki_EdgeConn_lemma_2_4_a
-- name    : NagamochiIbaraki.EdgeConn.lemma_2_4_a
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:03:07.650151+00:00
-- url     : https://prove2.me/theorems/ac954c04-81a7-4cb8-a649-a9a467cc2359
-- title:
--   Lemma 2.4(a) — when FOREST adds e = (u, v) to E_i, u and v are already joined by a path in E_{i−1}
-- statement:
--   Let $G = (V, E)$ be a finite multigraph without self-loops and with $|V| \ge 2$, and consider any execution of Procedure FOREST on $G$. Suppose that at some step FOREST adds an edge $e$ with end nodes $u, v$ to the class $E_i$ at line 7, where $i \ge 2$. Then, at that instant, there is a path
--
--   $$
--   P_{i-1} \subseteq E_{i-1}
--   $$
--
--   connecting $u$ and $v$.
--
--   Together with part (b) this shows that an edge that FOREST puts into a later class $E_j$ closes a cycle with every earlier class, which is the maximality half of Lemma 2.5.
--
--   **Formalization Note** The step at which $e$ is added is a step $\sigma_k \to \sigma_{k+1}$ of the run in which the index of $e$ changes from $0$ (unscanned) to $i$. The hypothesis $i \ge 2$ is added: for $i = 1$ the class $E_0$ does not exist and the statement has no content. "A path connecting $u$ and $v$" is reachability in the graph formed by the edges of $E_{i-1}$ (a path exists iff a walk does). $E_{i-1}$ is read in the state before the step; the step does not change it.
-- source:
--   Nagamochi, Ibaraki, A Linear-Time Algorithm for Finding a Sparse k-Connected Spanning Subgraph of a k-Connected Graph, Algorithmica 7 (1992), p. 588, Lemma 2.4(a)

import Mathlib
import Definitions.Def_NagamochiIbaraki_EdgeConn_Multigraph
import Definitions.Def_NagamochiIbaraki_EdgeConn_localEdgeConn
import Definitions.Def_NagamochiIbaraki_EdgeConn_Forest

namespace NagamochiIbaraki.EdgeConn

theorem lemma_2_4_a
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (hV : 2 ≤ Fintype.card V)
    (ends : E → Sym2 V) (hloop : ∀ e, ¬ (ends e).IsDiag)
    (σ : ℕ → State V E) (K : ℕ) (hrun : IsRun ends σ K) :
    ∀ k, k < K → ∀ (e : E) (i : ℕ) (u v : V),
      (σ k).idx e = 0 → (σ (k + 1)).idx e = i → ends e = s(u, v) → 2 ≤ i →
        (edgeGraph ends (cls (σ k) (i - 1))).Reachable u v := by sorry

end NagamochiIbaraki.EdgeConn
