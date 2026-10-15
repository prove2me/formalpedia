-- Prove2me | Theorems.Thm_LPCommunity_LPRecovery_proposition_1
-- name    : LPCommunity.LPRecovery.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T09:06:40.211959+00:00
-- url     : https://prove2.me/theorems/9e4ac073-51ab-410b-8c7a-ded2211c51d3
-- title:
--   Proposition 1, p. 7 — regular G1, G2, G0 with d_in − d_out ≥ n/4 − 1 make the planted cut vector optimal for (LP-P)
-- statement:
--   Let $n\ge 4$ and let $G$ be a graph on $V=\{1,\dots,n\}$ with planted bisection $V_1,V_2$. Suppose that $G_1=G[V_1]$ and $G_2=G[V_2]$ are both $d_{\mathrm{in}}$-regular for some $d_{\mathrm{in}}\in\{1,\dots,n/2-1\}$, and that the bipartite graph $G_0$ of crossing edges is $d_{\mathrm{out}}$-regular for some $d_{\mathrm{out}}\in\{0,\dots,n/2\}$. If
--   $$d_{\mathrm{in}}-d_{\mathrm{out}}\ \ge\ \frac n4-1, \qquad (5)$$
--   then the cut vector $\bar x$ of the planted bisection is an optimal solution of the metric relaxation (LP-P).
--
--   This is the optimality half of the paper's recovery result for regular graphs; Proposition 2 adds uniqueness under the slightly stronger condition $d_{\mathrm{in}}-d_{\mathrm{out}}\ge n/4$.
--
--   **Formalization Note** The standing assumptions of §3.1.1 (p. 7: $n\ge4$, $d_{\mathrm{in}}\in\{1,\dots,n/2-1\}$, $d_{\mathrm{out}}\in\{0,\dots,n/2\}$) are hypotheses. Regularity of $G_1$ and $G_2$ with the same degree is stated as "every vertex has exactly $d_{\mathrm{in}}$ neighbours on its own side". The case $d_{\mathrm{out}}=0$ is kept, as printed. All comparisons are in $\mathbb R$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 7, Proposition 1 (display (5)), with the §3.1.1 standing assumption (p. 7)

import Mathlib
import Definitions.Def_LPCommunity_LPRecovery_Setting

open Finset
open scoped Classical

namespace LPCommunity.LPRecovery

theorem proposition_1 {n : ℕ} (hn : 4 ≤ n) (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n))
    (hV1 : LPCommunity.MinBisect.IsBisection n V1) (din dout : ℕ) (hdin1 : 1 ≤ din) (hdin2 : (din : ℝ) ≤ (n : ℝ) / 2 - 1)
    (hdout : (dout : ℝ) ≤ (n : ℝ) / 2)
    (hin : ∀ v, LPCommunity.MinBisect.inDeg G V1 v = din) (hout : ∀ v, LPCommunity.MinBisect.outDeg G V1 v = dout)
    (h5 : (din : ℝ) - dout ≥ (n : ℝ) / 4 - 1) :
    LPOptimal G (cutVec V1) := by sorry

end LPCommunity.LPRecovery
