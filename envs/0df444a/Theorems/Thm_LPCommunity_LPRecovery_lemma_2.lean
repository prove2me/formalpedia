-- Prove2me | Theorems.Thm_LPCommunity_LPRecovery_lemma_2
-- name    : LPCommunity.LPRecovery.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:37.662194+00:00
-- url     : https://prove2.me/theorems/3e9d26a9-d32f-49a1-8f1c-a0c369a5dd69
-- title:
--   Lemma 2, p. 11 — deleting crossing edges preserves LP recovery
-- statement:
--   Characterize a graph $G$ with planted bisection $V_1,V_2$ by the triple $(G_0,G_1,G_2)$ of its crossing graph and its two induced subgraphs. Suppose the metric relaxation (LP-P) recovers the planted bisection for $(G_0,G_1,G_2)$. Let $\tilde G_0$ be a bipartite graph across the same bipartition with
--   $$E(\tilde G_0)\subseteq E(G_0).$$
--   Then (LP-P) also recovers the planted bisection for $(\tilde G_0,G_1,G_2)$.
--
--   With Lemma 3, this lets recovery for a regular graph be transferred to any graph sandwiched between regular ones, which is how Theorem 4 is obtained.
--
--   **Formalization Note** The second graph $G'$ has exactly the same edges as $G$ inside $V_1$ and inside $V_2$, and its crossing edges are crossing edges of $G$. The paper writes $E(\tilde G_0)\subset E(G_0)$ and its proof removes $m\ge1$ edges; the case of equality is trivial, so the inclusion is posed as $\subseteq$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 11, Lemma 2

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting

open Finset
open scoped Classical

namespace LPCommunity.LPRecovery

theorem lemma_2 {n : ℕ} (G G' : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : LPCommunity.MinBisect.IsBisection n V1) (hrec : LPRecovers G V1)
    (hsame : ∀ i j, LPCommunity.MinBisect.sameSide V1 i j → (G'.Adj i j ↔ G.Adj i j))
    (hcross : ∀ i j, ¬ LPCommunity.MinBisect.sameSide V1 i j → G'.Adj i j → G.Adj i j) :
    LPRecovers G' V1 := by sorry

end LPCommunity.LPRecovery
