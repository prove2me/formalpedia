-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_lemma_5_8_mean
-- name    : HarrisContact.MeanSize.lemma_5_8_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:25:08.261283+00:00
-- url     : https://prove2.me/theorems/ac5539be-8d48-4761-b1c1-8b2b0c24ba07
-- title:
--   Lemma 5.8 (m part), p. 978 — comparison: $\lambda_k \le \min_{j\ge k}\lambda'_j$ implies $m_t \le m'_t$
-- statement:
--   Let $(\xi_t)$ and $(\xi'_t)$ be contact processes on $Z_d$ with the same death rate $\mu\ge0$ and birth rates $\lambda_0=\lambda'_0=0$, $\lambda_k,\lambda'_k\ge0$ ($k\le 2d$). Suppose
--   $$\lambda_k\le\min_{k\le j\le 2d}\lambda'_j,\qquad k=1,\dots,2d.$$
--   Then the expected sizes satisfy
--   $$m_t(\xi)\le m'_t(\xi),\qquad t\ge0,$$
--   for every finite initial set $\xi$.
--
--   The paper's Lemma 5.8 also asserts $p_t(\xi)\le p'_t(\xi)$ for the survival probabilities; that half is not restated here. With the time-scale identity, this comparison reduces Theorem 7.6 to the linear rates $\mu=1$, $\lambda_k=k\lambda$.
--
--   **Formalization Note** The standing hypotheses of the contact process (Harris, §2(b), p. 971; §3, p. 972) are written as binders: $d \ge 1$, $\mu \ge 0$, $\lambda_0 = 0$ and $\lambda_k \ge 0$ for $0 \le k \le 2d$. Rates $\lambda_k$ with $k > 2d$ never enter the model, and no hypothesis mentions them. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$. The minimum over $j\ge k$ ranges over $k\le j\le 2d$, the indices the model uses. The paper states the lemma for all $\xi\in\Xi$; it is drafted for finite $\xi$.
-- source:
--   Harris (Ann. Probab. 2, 1974), Lemma 5.8, p. 978

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Lemma 5.8, p. 978, the `m_t` part: two contact processes with the same
death rate `μ` and birth rates `λ_k ≤ min_{j ≥ k} λ'_j` (`1 ≤ k ≤ 2d`) satisfy `m_t(ξ) ≤ m'_t(ξ)`. -/
theorem lemma_5_8_mean {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 ≤ μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (lam' : ℕ → ℝ) (h0' : lam' 0 = 0) (hlam' : ∀ k, k ≤ 2 * d → 0 ≤ lam' k)
    (hcomp : ∀ k j, 1 ≤ k → k ≤ j → j ≤ 2 * d → lam k ≤ lam' j) :
    ∀ t : ℝ, 0 ≤ t → ∀ ξ : HarrisContact.Extinction.Config d, HarrisContact.Extinction.meanSize μ lam t ξ ≤ HarrisContact.Extinction.meanSize μ lam' t ξ := by sorry
end HarrisContact.MeanSize
