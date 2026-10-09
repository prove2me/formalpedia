-- Prove2me | Theorems.Thm_ModernOnlineLearning_Bandits_theorem_9_17_adversarial
-- name    : ModernOnlineLearning.Bandits.theorem_9_17_adversarial
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:38:25.65925+00:00
-- url     : https://prove2.me/theorems/482d3fbc-142f-4af1-9f74-2826542fbecc
-- title:
--   Theorem 9.17, p. 165 — adversarial Tsallis-INF expected regret at most 32L∞√((d−1)T)
-- statement:
--   Fix $d\ge1$ arms, a horizon $T$, and an oblivious loss table satisfying $0\le g_{t,i}\le L_\infty$ with $L_\infty>0$. Run Tsallis-INF using the importance-weighted estimates and the FTRL update of Algorithm 9.6. For every fixed competitor arm $k$,
--
--   $$\mathbb E\!\left[\sum_{t=1}^{T}(g_{t,A_t}-g_{t,k})\right]\le32L_\infty\sqrt{(d-1)T}.$$
--
--   In particular, choosing the best arm of the fixed loss table gives the adversarial expected-regret guarantee in Theorem 9.17.
--
--   **Formalization Note** The only randomness is the algorithm's arm draws. Their law is the product of the round-by-round conditional probabilities. The update is required to be the FTRL minimizer for every history, with positive coordinates and predictable choices; these are properties of Algorithm 9.6. At $d=1$, regret and the bound both equal zero.
-- source:
--   Orabona, arXiv:1912.13213v10, Theorem 9.17, first claim, p. 165

import Definitions.Def_ModernOnlineLearning_Bandits_Tsallis
set_option autoImplicit false
noncomputable section

namespace ModernOnlineLearning.Bandits

/-- Orabona, Theorem 9.17, first claim, p. 165. This is expected regret
    against any fixed arm of the oblivious loss table. -/
theorem theorem_9_17_adversarial {T d : ℕ} (hd : 0 < d)
    (L : ℝ) (hL : 0 < L) (anchor : Fin d)
    (g : ℕ → Fin d → ℝ)
    (x : ArmPath T d → ℕ → Fin d → ℝ)
    (hBound : ∀ t ∈ Finset.Icc 1 T, ∀ i, 0 ≤ g t i ∧ g t i ≤ L)
    (hRun : IsTsallisRun L g x) (k : Fin d) :
    expectedRegret anchor g x k ≤
      32 * L * Real.sqrt (((d : ℝ) - 1) * (T : ℝ)) := by sorry

end ModernOnlineLearning.Bandits
