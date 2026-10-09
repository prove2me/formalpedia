-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_equation_9
-- name    : OnlineCombOpt.BanditLB.equation_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:11.168166+00:00
-- url     : https://prove2.me/theorems/4b3aa69a-3909-4810-ab48-740f30566815
-- title:
--   Equation (9), p. 17 — regret identity and maximum at least mean
-- statement:
--   Fix $n\ge1$, $k\ge2$, $m$ parallel games, a deterministic bandit player, and $0\le\epsilon\le1/2$. For every $\alpha$, the pseudo-regret $\bar R_n(\alpha)$ of the player against the $\alpha$-adversary (its expected cumulative loss minus the smallest expected cumulative loss of a fixed action) is
--
--   $$
--   \bar R_n(\alpha)=n\epsilon\sum_{i=1}^m\bigl(1-\mathbb P_{i,\alpha}(1)\bigr).
--   $$
--
--   Consequently, since the maximum is at least the mean, some $\alpha$ satisfies
--
--   $$
--   \bar R_n(\alpha)\ge n\epsilon\sum_{i=1}^m\Bigl(1-\frac1{k^m}\sum_{\beta}\mathbb P_{i,\beta}(1)\Bigr).
--   $$
--
--   This is the first averaging step of the lower-bound proof.
--
--   **Formalization Note** $k=d/m$ and $k^m=(d/m)^m$. The minimum in the regret is over all $k^m$ actions; the identity includes the fact that $\alpha$ is optimal against its own adversary. The parameter $k$ is at least two because $d\ge2m$ in Theorem 5.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 17, Appendix B, equation (9)

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Games

namespace OnlineCombOpt.BanditLB

theorem equation_9 (n m k : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (hn : 1 ≤ n) (hk : 2 ≤ k) (hε : 0 ≤ ε ∧ ε ≤ (1 : ℝ) / 2) :
    (∀ α : GameAction m k,
      gamesRegret n ε f α = n * ε * ∑ i : Fin m, (1 - pAlpha n ε f i α)) ∧
    (∃ α : GameAction m k,
      n * ε * ∑ i : Fin m,
        (1 - (∑ β : GameAction m k, pAlpha n ε f i β) / (k : ℝ)^m) ≤
      gamesRegret n ε f α) := by sorry

end OnlineCombOpt.BanditLB
