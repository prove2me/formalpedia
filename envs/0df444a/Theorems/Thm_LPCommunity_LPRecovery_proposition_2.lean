-- Prove2me | Theorems.Thm_LPCommunity_LPRecovery_proposition_2
-- name    : LPCommunity.LPRecovery.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:38.129027+00:00
-- url     : https://prove2.me/theorems/0d4d95cd-bca1-4324-add8-5c20d08e5b78
-- title:
--   Proposition 2, p. 10 — regular G1, G2, G0 with d_in − d_out ≥ n/4 make (LP-P) recover the planted bisection
-- statement:
--   Let $G$ be a graph on $V=\{1,\dots,n\}$ with planted bisection $V_1,V_2$. Suppose that $G_1=G[V_1]$ and $G_2=G[V_2]$ are both $d_{\mathrm{in}}$-regular and that the bipartite graph $G_0$ of crossing edges is $d_{\mathrm{out}}$-regular. If
--   $$d_{\mathrm{in}}-d_{\mathrm{out}}\ \ge\ \frac n4, \qquad (13)$$
--   then the metric relaxation (LP-P) recovers the planted bisection: the cut vector $\bar x$ is its unique optimal solution.
--
--   Together with Theorem 2 of the paper, this shows that the worst-case recovery condition for the LP relaxation on regular instances is tight.
--
--   **Formalization Note** The §3.1.1 standing ranges ($n\ge4$, $1\le d_{\mathrm{in}}\le n/2-1$, $0\le d_{\mathrm{out}}\le n/2$) are not hypotheses: on a bisection they are implied by the regularity hypotheses and (13) whenever $n\ge4$; for $n=2$ the hypotheses cannot hold (the inside degree is $0<1/2$), and for $n=0$ the conclusion holds trivially. The statement is therefore the paper's, with no range hypotheses to add. All comparisons are in $\mathbb R$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 10, Proposition 2 (display (13))

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting

open Finset
open scoped Classical

namespace LPCommunity.LPRecovery

theorem proposition_2 {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : LPCommunity.MinBisect.IsBisection n V1) (din dout : ℕ)
    (hin : ∀ v, LPCommunity.MinBisect.inDeg G V1 v = din) (hout : ∀ v, LPCommunity.MinBisect.outDeg G V1 v = dout)
    (h13 : (din : ℝ) - dout ≥ (n : ℝ) / 4) :
    LPRecovers G V1 := by sorry

end LPCommunity.LPRecovery
