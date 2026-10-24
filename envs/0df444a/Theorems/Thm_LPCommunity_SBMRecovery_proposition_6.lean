-- Prove2me | Theorems.Thm_LPCommunity_SBMRecovery_proposition_6
-- name    : LPCommunity.SBMRecovery.proposition_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:22.020173+00:00
-- url     : https://prove2.me/theorems/b4f1a35a-c3a7-41fe-9919-3783a79ab838
-- title:
--   Proposition 6, p. 20 — the maximum degree of G_{2m,0,q} is at most qm + C√(m log m) w.h.p.
-- statement:
--   Fix $q\in(0,1)$ and let $G\sim\mathcal G_{2m,0,q}$: a bisection $V_1,V_2$ of $2m$ nodes is chosen uniformly at random and each of the $m^2$ pairs between $V_1$ and $V_2$ is an edge independently with probability $q$; there are no edges inside $V_1$ or $V_2$. Let $d_{\max}$ be the maximum node degree of $G$. Then there is a constant $C>0$ such that
--   $$
--   \mathbb P\Big[d_{\max}\le qm+C\sqrt{m\log m}\Big]\longrightarrow 1\qquad (m\to\infty).
--   $$
--
--   Since $qm$ is the expected degree, this says that all degrees of the random bipartite graph concentrate within $O(\sqrt{m\log m})$ of their mean. It is the first ingredient of Proposition 3.
--
--   **Formalization Note** The constant $C$ may depend on $q$ (as printed, $q$ is fixed first) but not on $m$. For $m\le 1$, $\log m\le 0$ and the bound degenerates; this affects finitely many $m$ only.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 20, Proposition 6

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Factors

open Finset Filter Topology
open scoped Classical

namespace LPCommunity.SBMRecovery

/-- Proposition 6 (p. 20): for `G ∼ G_{2m,0,q}` with `q ∈ (0,1)` there is `C > 0` such that, with high
probability, `d_max ≤ qm + C √(m log m)`. -/
theorem proposition_6 (q : ℝ) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun m : ℕ => sbmProb (2 * m) 0 q
        (fun _ G => (dMax G : ℝ) ≤ q * m + C * Real.sqrt (m * Real.log m))) atTop (𝓝 1) := by sorry

end LPCommunity.SBMRecovery
