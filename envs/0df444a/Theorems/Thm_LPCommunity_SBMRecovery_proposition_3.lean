-- Prove2me | Theorems.Thm_LPCommunity_SBMRecovery_proposition_3
-- name    : LPCommunity.SBMRecovery.proposition_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:45.455726+00:00
-- url     : https://prove2.me/theorems/5d6f3dfe-35fe-4ae4-9bf2-9c7190b90e5d
-- title:
--   Proposition 3, p. 14 — G_{n,0,q} lies in a ⌊d_reg⌋-regular bipartite graph with the same bipartition w.h.p.
-- statement:
--   There is a constant $C_{\mathrm{reg},2}>0$ such that for every $q\in(0,1)$ the following holds. Let $n=2m$ and $G\sim\mathcal G_{n,0,q}$, with planted bisection $V_1,V_2$, and put
--   $$
--   d_{\mathrm{reg}}=\frac{qn}{2}+C_{\mathrm{reg},2}\sqrt{\frac n2\log\frac n2}.
--   $$
--   Then, with probability tending to $1$ as $n\to\infty$, there is a graph $H$ on the same nodes such that $G\subseteq H$, every edge of $H$ joins $V_1$ to $V_2$ (so $H$ is bipartite with the same bipartition), and every node of $H$ has degree $\lfloor d_{\mathrm{reg}}\rfloor$.
--
--   In the proof of Theorem 6 this is applied to the bipartite graph $G_0$ of edges between the communities: one may add edges to $G_0$ to make it regular of degree about $qn/2$, as Theorem 4 requires.
--
--   **Formalization Note** The printed $d_{\mathrm{reg}}$ is in general not an integer, while a regular graph has an integer degree. The statement is posed with the degree $\lfloor d_{\mathrm{reg}}\rfloor$ (so $G_0$ lies in a regular bipartite graph of degree at most $d_{\mathrm{reg}}$), which is the reading Theorem 6 uses. The constant is chosen before $q$, as printed. The bipartition of $H$ is the drawn planted bisection.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 14, Proposition 3

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open Finset Filter Topology
open scoped Classical

namespace LPCommunity.SBMRecovery

/-- Proposition 3 (p. 14): there is `C_reg,2 > 0` such that for every `q ∈ (0,1)`, with high probability
`G ∼ G_{n,0,q}` (`n = 2m`) is a subgraph of a regular bipartite graph with the planted bipartition
`V1, V1ᶜ`, of degree `⌊d_reg⌋`, `d_reg = qn/2 + C_reg,2 √((n/2) log(n/2))`. -/
theorem proposition_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ q : ℝ, 0 < q → q < 1 →
      Tendsto (fun m : ℕ => sbmProb (2 * m) 0 q (fun V1 G =>
        ∃ H : SimpleGraph (Fin (2 * m)), G ≤ H ∧ (∀ i j, H.Adj i j → ¬ LPCommunity.MinBisect.sameSide V1 i j) ∧
          ∀ v, (H.degree v : ℤ) = ⌊q * m + C * Real.sqrt (m * Real.log m)⌋)) atTop (𝓝 1) := by sorry

end LPCommunity.SBMRecovery
