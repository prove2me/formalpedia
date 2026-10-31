-- Prove2me | Theorems.Thm_MNLTrisection_Adaptive_lemma_11
-- name    : MNLTrisection.Adaptive.lemma_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:35.439471+00:00
-- url     : https://prove2.me/theorems/bef59ff9-b0d8-4d67-9b10-3714a967677e
-- title:
--   Lemma 11, p. 13 — regret in Case 3: ψ³_τ(α, β) ≤ αT
-- statement:
--   Throughout, there are $N$ items with known revenues $r_i \in [0,1]$ and unknown utilities $v_i \ge 0$, the no-purchase utility is $v_0 = 1$, and $R(S) = \sum_{j\in S} r_j v_j/(1+\sum_{j\in S} v_j)$ is the expected revenue (2) of an assortment $S \subseteq [N]$. Run the adaptive-confidence trisection policy for $T$ periods. For an epoch $\tau$ and $\alpha, \beta \ge 0$, let $\psi^3_\tau(\alpha,\beta)$ be the expected regret of epochs $\tau, \tau+1, \dots, \tau_0$ conditioned on the event $\mathcal E_3(\tau) : a_\tau < b_\tau < \theta^*$ (with epoch $\tau$ started), $|a_\tau - \theta^*| = \alpha$ and $|F(a_\tau) - a_\tau| = \beta$, as in (14). Then
--   $$\psi^3_\tau(\alpha,\beta) \le \alpha T.$$
--
--   When the search interval lies entirely below the optimal level, every later offer is a level set between $a_\tau$ and $\theta^*$, and each costs at most $\alpha$.
--
--   **Formalization Note** $\psi$ is the conditional expectation on the finite space of purchase histories (a ratio of finite sums), and is $0$ on a conditioning event of probability $0$. $\theta^* = F^*$.
-- source:
--   Chen, Wang & Zhou, An Optimal Policy for Dynamic Assortment Planning Under Uncapacitated Multinomial Logit Models, arXiv:1805.04785v2, p. 13, Lemma 11 and (14); proof in Supplement p. 8 (PDF 27)

import Mathlib
import Definitions.Def_MNLTrisection_Adaptive_Model

namespace MNLTrisection.Adaptive

/-- **Lemma 11** (Regret in Case 3, p. 13). `ψ³_τ(α, β) ≤ αT`. -/
theorem lemma_11 {N : ℕ} (v r : Fin N → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hr : ∀ i, r i ∈ Set.Icc (0 : ℝ) 1) (T τ : ℕ) (α β : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    psi v r T 3 τ α β ≤ α * T := by sorry

end MNLTrisection.Adaptive
