-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_horizon_kl
-- name    : OnlineCombOpt.BanditLB.horizon_kl
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:27.207967+00:00
-- url     : https://prove2.me/theorems/0be300c2-865d-4db9-b9d4-9dc91e635918
-- title:
--   Appendix B, p. 18 — data processing and horizon KL bound
-- statement:
--   For a deterministic bandit player in $m$ games of $k\ge2$ actions, a game $i$ and an action $\alpha$, let $\mathbb P^n_\alpha$ and $\mathbb P^n_{-i,\alpha}$ be the laws of the observed loss sequence $W_n$ over $n\ge1$ rounds against the $\alpha$-adversary and the $(-i,\alpha)$-adversary, and let $\mathbb P_{i,\alpha}$, $\mathbb P_{-i,\alpha}$ be the laws of the event that the favoured action of game $i$ is chosen at a uniformly chosen round. If $0<\epsilon<1/2$, then
--
--   $$
--   \mathrm{KL}(\mathbb P_{-i,\alpha},\mathbb P_{i,\alpha})\le\mathrm{KL}(\mathbb P^n_{-i,\alpha},\mathbb P^n_\alpha)\le\frac{8\epsilon^2 n}{(1-4\epsilon^2)m}\,\mathbb P_{-i,\alpha}(1).
--   $$
--
--   The first inequality holds because $W_n$ determines the plays of a deterministic player; the second is the chain-rule estimate of the whole observed history.
--
--   **Formalization Note** Every divergence puts the $(-i,\alpha)$ law first. The observations take values in $\{0,\ldots,m\}$ under these adversaries, but the player's decision rule accepts arbitrary real-valued histories.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 18, Appendix B, third step

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Games

namespace OnlineCombOpt.BanditLB

theorem horizon_kl (n m k : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (α : GameAction m k)
    (hn : 1 ≤ n) (hk : 2 ≤ k) (hε : 0 < ε ∧ ε < (1 : ℝ) / 2) :
    klFin (choiceLawMinus n ε f i α) (choiceLaw n ε f i α) ≤
        klFin (lawWMinus n ε f i α) (lawW n ε f α) ∧
    klFin (lawWMinus n ε f i α) (lawW n ε f α) ≤
      (8 * ε^2 * n / ((1 - 4 * ε^2) * m)) * pMinus n ε f i α := by sorry

end OnlineCombOpt.BanditLB
