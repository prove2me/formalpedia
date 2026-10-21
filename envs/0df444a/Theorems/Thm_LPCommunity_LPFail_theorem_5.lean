-- Prove2me | Theorems.Thm_LPCommunity_LPFail_theorem_5
-- name    : LPCommunity.LPFail.theorem_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:26.356459+00:00
-- url     : https://prove2.me/theorems/9e31207f-ca9d-469a-9f33-3bea001b343a
-- title:
--   Theorem 5, p. 12 — if (1 + c(G))|E|/(2ρ_avg + 2c(G)(1 − 1/n)) < |E0|, the metric LP does not recover the planted bisection
-- statement:
--   Let $G=(V,E)$ be a connected graph on $n\ge 5$ nodes with a planted bisection $V_1,V_2$, and let $E_0$ be the set of edges joining $V_1$ and $V_2$. Let $\rho_{\max}(G)$ and $\rho_{\mathrm{avg}}(G)$ be the diameter and the average distance of $G$, and define
--   $$c(G):=\max\Big\{0,\ \frac{3\rho_{\max}(G)-4\rho_{\mathrm{avg}}(G)}{1-\frac4n}\Big\}.\qquad(17)$$
--   If
--   $$\frac{1+c(G)}{2\rho_{\mathrm{avg}}(G)+2c(G)(1-\frac1n)}\,|E|<|E_0|,\qquad(18)$$
--   then the LP relaxation (LP-P) does not recover the planted bisection, i.e. the cut vector of $V_1,V_2$ is not the unique optimal solution of (LP-P).
--
--   This is the paper's necessary condition for LP recovery. Applied to random graphs, where the average distance is close to the diameter, it shows that the metric relaxation seldom recovers the planted partition (Theorems 7 and 8).
--
--   **Formalization Note** The planted bisection, implicit in the page's "Let $G=(V,E)$", is a hypothesis ($2|V_1|=n$); with it $n$ is even, so in effect $n\ge 6$. The bound $n\ge5$ is kept as printed. $|E_0|$ is the number of edges of $G$ crossing $V_1,V_1^{c}$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 12, Theorem 5, displays (17)–(18)

import Mathlib
import Definitions.Def_LPCommunity_LPFail_Setting

open Finset
open scoped Classical ENNReal

namespace LPCommunity.LPFail
theorem theorem_5 {n : ℕ} (G : SimpleGraph (Fin n)) (V1 : Finset (Fin n)) (hV1 : LPCommunity.MinBisect.IsBisection n V1)
    (hconn : G.Connected) (hn : 5 ≤ n)
    (h18 : (1 + cG G) / (2 * (rhoAvg G).toReal + 2 * cG G * (1 - 1 / (n : ℝ))) *
        (G.edgeFinset.card : ℝ) < (LPCommunity.MinBisect.cutCost G V1 : ℝ)) :
    ¬ LPCommunity.LPRecovery.LPRecovers G V1 := by sorry
end LPCommunity.LPFail
