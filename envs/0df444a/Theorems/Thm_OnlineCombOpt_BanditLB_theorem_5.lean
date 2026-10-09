-- Prove2me | Theorems.Thm_OnlineCombOpt_BanditLB_theorem_5
-- name    : OnlineCombOpt.BanditLB.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:44.37344+00:00
-- url     : https://prove2.me/theorems/0191e881-940a-4c1f-913c-5a5c2d6acd35
-- title:
--   Theorem 5, p. 14 — bandit regret lower bound
-- statement:
--   Let $n,d,m$ be nonnegative integers with $n\ge d\ge2m$ and $m\mid d$. There is a nonempty finite action set $\mathcal A\subseteq\{0,1\}^d$ whose every member selects exactly $m$ coordinates. For every randomized bandit strategy on $\mathcal A$, there is a finite-support randomized loss sequence in $[0,1]^{n\times d}$ for which
--
--   $$
--   R_n\ge0.02\,m\sqrt{dn},\qquad
--   R_n=\mathbb E\sum_{t=1}^n a_t^\mathsf Tz_t-\min_{a\in\mathcal A}\mathbb E\sum_{t=1}^n a^\mathsf Tz_t.
--   $$
--
--   The theorem proves a minimax lower bound for online combinatorial optimization with bandit feedback.
--
--   **Formalization Note** The additional condition $m\mid d$ is the simplification explicitly used in Appendix B and is needed for the stated constant by this construction. The exhibited adversary is oblivious and finitely supported, a strengthening of the existential claim. Strategies are behavioural: a probability vector on $\mathcal A$ for each history of past actions and real-valued scalar observations $a_s^\mathsf Tz_s$; this covers every randomized player (the paper's $p_s$ are functions of the earlier history). The player never sees $z_t$ itself. At $m=d=0$ the bound is zero.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 14, Theorem 5; p. 16, Appendix B

import Mathlib
import Definitions.Def_OnlineCombOpt_BanditLB_Setting

namespace OnlineCombOpt.BanditLB

theorem theorem_5 (n d m : ℕ) (hn : d ≤ n) (hd : 2 * m ≤ d)
    (hdiv : m ∣ d) :
    ∃ A : Finset (Fin d → ℝ), OnlineCombOpt.Exp2LB.IsBinaryActionSet A m ∧
      ∀ σ : BanditStrategy d, IsStrategyOn A σ →
        ∃ (Z : Finset (Fin n → Fin d → ℝ))
          (μ : (Fin n → Fin d → ℝ) → ℝ),
          IsObliviousAdversary Z μ ∧
          ((2 : ℝ) / 100) * m * Real.sqrt ((d : ℝ) * n) ≤
            banditRegret A σ Z μ := by sorry

end OnlineCombOpt.BanditLB
