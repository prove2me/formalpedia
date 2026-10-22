-- Prove2me | Theorems.Thm_LPCommunity_LPRecovery_lemma_3
-- name    : LPCommunity.LPRecovery.lemma_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:46.978706+00:00
-- url     : https://prove2.me/theorems/5193b2b2-5330-4a38-ab67-91469c3abd6e
-- title:
--   Lemma 3, p. 11 — adding edges inside the communities preserves LP recovery
-- statement:
--   Characterize a graph $G$ with planted bisection $V_1,V_2$ by the triple $(G_0,G_1,G_2)$ of its crossing graph and its two induced subgraphs. Suppose the metric relaxation (LP-P) recovers the planted bisection for $(G_0,G_1,G_2)$. Let $\tilde G_1$, $\tilde G_2$ be graphs on $V_1$, $V_2$ with
--   $$E(\tilde G_1)\supseteq E(G_1),\qquad E(\tilde G_2)\supseteq E(G_2).$$
--   Then (LP-P) also recovers the planted bisection for $(G_0,\tilde G_1,\tilde G_2)$.
--
--   Adding edges inside the communities can only help the LP single out the planted bisection; with Lemma 2 this extends Proposition 2 from regular to sandwiched graphs.
--
--   **Formalization Note** The second graph $G'$ has exactly the same crossing edges as $G$, and every edge of $G$ inside $V_1$ or inside $V_2$ is an edge of $G'$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 11, Lemma 3

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting

open Finset
open scoped Classical

namespace LPCommunity.LPRecovery

theorem lemma_3 {n : ℕ} (G G' : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : LPCommunity.MinBisect.IsBisection n V1) (hrec : LPRecovers G V1)
    (hcross : ∀ i j, ¬ LPCommunity.MinBisect.sameSide V1 i j → (G'.Adj i j ↔ G.Adj i j))
    (hsame : ∀ i j, LPCommunity.MinBisect.sameSide V1 i j → G.Adj i j → G'.Adj i j) :
    LPRecovers G' V1 := by sorry

end LPCommunity.LPRecovery
