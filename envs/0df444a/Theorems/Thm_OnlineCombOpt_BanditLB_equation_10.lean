-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_equation_10
-- name    : OnlineCombOpt.BanditLB.equation_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:56:40.51333+00:00
-- url     : https://prove2.me/theorems/d371589c-fe91-4fba-9a64-38ed2fa90ea2
-- title:
--   Equation (10), p. 17 — symmetry of the minus-i adversaries
-- statement:
--   Fix a game $i$ among $m$ parallel games with $k\ge2$ actions each, a positive horizon, and a deterministic player. For $0\le\epsilon<1/2$, average the probability $P_{-i,\alpha}(1)$ over all $k^m$ favoured actions $\alpha$. The result is
--
--   $$
--   \frac1{k^m}\sum_{\alpha}P_{-i,\alpha}(1)=\frac1k=\frac md.
--   $$
--
--   The symmetry removes the player-dependent baseline term from the information inequality.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 17, Appendix B, equation (10)

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Games

namespace OnlineCombOpt.BanditLB

theorem equation_10 (n m k : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hε : 0 ≤ ε ∧ ε < (1 : ℝ) / 2) :
    (∑ α : GameAction m k, pMinus n ε f i α) / (k : ℝ)^m = 1 / (k : ℝ) := by sorry

end OnlineCombOpt.BanditLB
