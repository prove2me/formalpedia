-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_averaged_bound
-- name    : OnlineCombOpt.BanditLB.averaged_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:11.966663+00:00
-- url     : https://prove2.me/theorems/b65e12d2-3466-462e-bc90-ff1e4450a457
-- title:
--   Appendix B, p. 18 — averaged probability of finding the favoured choice
-- statement:
--   For a deterministic bandit player in $m$ parallel games with $k\ge2$ actions, a positive horizon, a game $i$, and $0<\epsilon\le1/\sqrt8$, one has
--
--   $$
--   \frac1{k^m}\sum_\alpha P_{i,\alpha}(1)\le\frac1k+\epsilon\sqrt{\frac{8n}{mk}}.
--   $$
--
--   Since $d=mk$, this is the displayed bound $m/d+\epsilon\sqrt{8n/d}$ used with equation (9) to reach Theorem 5.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 18, Appendix B, display after “Summing and plugging this into (11)”

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Games

namespace OnlineCombOpt.BanditLB

theorem averaged_bound (n m k : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hε : 0 < ε ∧ ε ≤ 1 / Real.sqrt 8) :
    (∑ α : GameAction m k, pAlpha n ε f i α) / (k : ℝ)^m ≤
      1 / (k : ℝ) + ε * Real.sqrt (8 * n / ((m : ℝ) * k)) := by sorry

end OnlineCombOpt.BanditLB
