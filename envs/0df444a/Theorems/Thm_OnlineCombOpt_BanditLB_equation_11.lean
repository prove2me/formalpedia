-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_equation_11
-- name    : OnlineCombOpt.BanditLB.equation_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:11.67272+00:00
-- url     : https://prove2.me/theorems/f9fe5aa0-a922-4aad-9bd9-d4ce3cb8f6f8
-- title:
--   Equation (11), p. 17 — averaged Pinsker bound
-- statement:
--   For a deterministic player in $m$ games of $k\ge2$ actions, a horizon $n\ge1$, a game $i$ and $0<\epsilon<1/2$, let $\mathbb P_{i,\alpha}$ and $\mathbb P_{-i,\alpha}$ be the laws on $\{0,1\}$ of the event that the player selects the favoured action of game $i$ at a uniformly chosen round, against the $\alpha$-adversary and the $(-i,\alpha)$-adversary. Then:
--
--   1. (Pinsker) for every $\alpha$,
--   $$
--   \mathbb P_{i,\alpha}(1)\le\mathbb P_{-i,\alpha}(1)+\sqrt{\tfrac12\mathrm{KL}(\mathbb P_{-i,\alpha},\mathbb P_{i,\alpha})};
--   $$
--   2. averaged over all $k^m$ actions $\alpha$,
--   $$
--   \frac1{k^m}\sum_\alpha \mathbb P_{i,\alpha}(1)\le\frac1k+\sqrt{\frac1{2k^m}\sum_\alpha\mathrm{KL}(\mathbb P_{-i,\alpha},\mathbb P_{i,\alpha})}.
--   $$
--
--   This converts a bound on the information in the observations into a bound on how often the player finds the favoured action. With $d=mk$, $1/k=m/d$.
--
--   **Formalization Note** The KL direction is $\mathbb P_{-i,\alpha}$ first. Pinsker's inequality and the symmetry (10) are proof tools, not hypotheses.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 17, Appendix B, equation (11)

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Games

namespace OnlineCombOpt.BanditLB

theorem equation_11 (n m k : ℕ) (ε : ℝ) (f : DetPlayer m k)
    (i : Fin m) (hn : 1 ≤ n) (hk : 2 ≤ k)
    (hε : 0 < ε ∧ ε < (1 : ℝ) / 2) :
    (∀ α : GameAction m k,
      pAlpha n ε f i α ≤ pMinus n ε f i α +
        Real.sqrt ((1 / 2) * klFin (choiceLawMinus n ε f i α) (choiceLaw n ε f i α))) ∧
    (∑ α : GameAction m k, pAlpha n ε f i α) / (k : ℝ)^m ≤
      1 / (k : ℝ) +
      Real.sqrt ((∑ α : GameAction m k,
        klFin (choiceLawMinus n ε f i α) (choiceLaw n ε f i α)) /
        (2 * (k : ℝ)^m)) := by sorry

end OnlineCombOpt.BanditLB
