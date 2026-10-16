-- Prove2me | Theorems.Thm_LPCommunity_SBMRecovery_proposition_4
-- name    : LPCommunity.SBMRecovery.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T11:05:02.550345+00:00
-- url     : https://prove2.me/theorems/9f7e650e-a1e3-4c54-8230-72f1a861f094
-- title:
--   Proposition 4, p. 14 — G_{n,p} contains a spanning regular subgraph of degree about pn − C_reg,1 √(n log n) w.h.p.
-- statement:
--   There is a constant $C_{\mathrm{reg},1}>0$ such that for every $p\in(0,1)$ the following holds. Let $G\sim\mathcal G_{n,p}$ and
--   $$
--   d_{\mathrm{reg}}=pn-C_{\mathrm{reg},1}\sqrt{n\log n}.
--   $$
--   Then, with probability tending to $1$ as $n\to\infty$, $G$ contains a spanning subgraph $H$ (same node set, $H\subseteq G$) in which every node has degree $2\lceil d_{\mathrm{reg}}/2\rceil$, the least even integer $\ge d_{\mathrm{reg}}$.
--
--   In the proof of Theorem 6 this is applied to the two communities $G_1,G_2$ (each an Erdős–Rényi graph on $n/2$ nodes): one may delete edges inside each community to make both regular of the same degree, about $pn/2$, as Theorem 4 requires.
--
--   **Formalization Note** The printed $d_{\mathrm{reg}}$ is in general not an integer. The proof (p. 24) says "without loss of generality, we may suppose $d_{\mathrm{reg}}$ is even"; the statement is posed with the explicit even integer $2\lceil d_{\mathrm{reg}}/2\rceil$, which also makes a regular graph possible on an odd number of nodes, and gives one degree that serves both communities. The constant is chosen before $p$, as printed.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 14, Proposition 4 (proof in §5.2, pp. 24–26)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting

open Finset Filter Topology
open scoped Classical

namespace LPCommunity.SBMRecovery

/-- Proposition 4 (p. 14): there is `C_reg,1 > 0` such that for every `p ∈ (0,1)`, with high
probability `G ∼ G_{n,p}` contains a spanning regular subgraph of degree `2⌈d_reg/2⌉` (the least even
integer `≥ d_reg`), `d_reg = pn − C_reg,1 √(n log n)`. -/
theorem proposition_4 :
    ∃ C : ℝ, 0 < C ∧ ∀ p : ℝ, 0 < p → p < 1 →
      Tendsto (fun n : ℕ => erProb n p (fun G =>
        ∃ H : SimpleGraph (Fin n), H ≤ G ∧
          ∀ v, (H.degree v : ℤ) = 2 * ⌈(p * n - C * Real.sqrt (n * Real.log n)) / 2⌉))
        atTop (𝓝 1) := by sorry

end LPCommunity.SBMRecovery
