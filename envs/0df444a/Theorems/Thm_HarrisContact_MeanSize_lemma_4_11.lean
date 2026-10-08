-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_lemma_4_11
-- name    : HarrisContact.MeanSize.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:28:03.917522+00:00
-- url     : https://prove2.me/theorems/5a2e1b67-c41e-416f-9eb9-349ef5df9478
-- title:
--   Lemma 4.11, p. 976 — $m_{t+h}(\xi) \ge e^{-\mu h} m_t(\xi)$
-- statement:
--   Let $(\xi_t)$ be a contact process on $Z_d$ with death rate $\mu\ge0$ and birth rates $\lambda_0=0$, $\lambda_k\ge0$. Then for every finite $\xi$,
--   $$m_{t+h}(\xi)\ge e^{-\mu h}\,m_t(\xi),\qquad t\ge0,\ h\ge0.$$
--
--   The expected size can decrease no faster than pure death at rate $\mu$ would make it. Combined with Theorem 7.6 it yields $m_t(\xi)\to0$ (Remark 7.12).
--
--   **Formalization Note** The standing hypotheses of the contact process (Harris, §2(b), p. 971; §3, p. 972) are written as binders: $d \ge 1$, $\mu \ge 0$, $\lambda_0 = 0$ and $\lambda_k \ge 0$ for $0 \le k \le 2d$. Rates $\lambda_k$ with $k > 2d$ never enter the model, and no hypothesis mentions them. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$. The paper states the lemma for all $\xi\in\Xi$; it is drafted for finite $\xi$.
-- source:
--   Harris (Ann. Probab. 2, 1974), Lemma 4.11, p. 976

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Lemma 4.11, p. 976: `m_{t+h}(ξ) ≥ e^{−μh} m_t(ξ)` for `t, h ≥ 0`
(drafted for finite `ξ`). -/
theorem lemma_4_11 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k) :
    ∀ t h : ℝ, 0 ≤ t → 0 ≤ h → ∀ ξ : HarrisContact.Extinction.Config d,
      ENNReal.ofReal (Real.exp (-(μ * h))) * HarrisContact.Extinction.meanSize μ lam t ξ ≤ HarrisContact.Extinction.meanSize μ lam (t + h) ξ := by sorry
end HarrisContact.MeanSize
