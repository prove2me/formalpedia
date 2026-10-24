-- Prove2me | Theorems.Thm_LPCommunity_SBMRecovery_proposition_8
-- name    : LPCommunity.SBMRecovery.proposition_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:04:47.287013+00:00
-- url     : https://prove2.me/theorems/dea85c89-ec56-42fe-80ae-5083591a9602
-- title:
--   Proposition 8, p. 24 — the minimum degree of G_{n,p} is at least pn − C√(n log n) w.h.p.
-- statement:
--   Fix $p\in(0,1)$ and let $G\sim\mathcal G_{n,p}$. Let $d_{\min}$ be the minimum node degree of $G$. Then there is a constant $C>0$ such that
--   $$
--   \mathbb P\Big[d_{\min}\ge pn-C\sqrt{n\log n}\Big]\longrightarrow 1\qquad(n\to\infty).
--   $$
--
--   The paper cites Chapter 3 of Frieze–Karoński, *Introduction to Random Graphs*. It is the degree estimate used in the proof of Proposition 4.
--
--   **Formalization Note** The constant may depend on $p$ (as printed, $p$ is fixed first) but not on $n$.
-- source:
--   Del Pia, Khajavirad, Kunisky, Linear Programming and Community Detection, arXiv:2006.03213v2, p. 24, Proposition 8 (Chapter 3 of Frieze–Karoński)

import Mathlib
import Definitions.Def_LPCommunity_SBMRecovery_Setting
import Definitions.Def_LPCommunity_SBMRecovery_Factors

open Finset Filter Topology
open scoped Classical

namespace LPCommunity.SBMRecovery

/-- Proposition 8 (p. 24): for `G ∼ G_{n,p}` with `p ∈ (0,1)` there is `C > 0` such that, with high
probability, `d_min ≥ pn − C √(n log n)`. -/
theorem proposition_8 (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ C : ℝ, 0 < C ∧
      Tendsto (fun n : ℕ => erProb n p
        (fun G => (dMin G : ℝ) ≥ p * n - C * Real.sqrt (n * Real.log n))) atTop (𝓝 1) := by sorry

end LPCommunity.SBMRecovery
