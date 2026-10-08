-- Prove2me | Theorems.Thm_HarrisContact_MeanSize_remark_7_12
-- name    : HarrisContact.MeanSize.remark_7_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:27:17.033986+00:00
-- url     : https://prove2.me/theorems/5e79887a-9477-490a-b2da-40816b962d5e
-- title:
--   Remark 7.12, p. 982 — under Theorem 7.6's conditions, $m_t(\xi)\to0$
-- statement:
--   Under the conditions of Theorem 7.6 — death rate $\mu>0$, birth rates $\lambda_0=0$, $\lambda_k\ge0$ with $\lambda_k/\mu<k/(2d-1)$ for $k=1,\dots,2d$, $d\ge1$ — the expected size of the contact process started from any finite $\xi$ tends to zero:
--   $$\lim_{t\to\infty}m_t(\xi)=0 .$$
--
--   The paper derives it from Theorem 7.6 and Lemma 4.11.
--
--   **Formalization Note** The hypotheses are exactly those of the Theorem 7.6 item, including the explicit $\mu>0$. The limit is taken in $[0,\infty]$. The process is the countable-state chain on finite configurations of §4 (p. 975), with transition function the minimal solution $P_t$ of the backward equations for the rates (4.4)–(4.5); $m_t(\xi)=\sum_\eta P_t(\xi,\eta)\,|\eta|$ is an extended nonnegative real, so a divergent sum is $+\infty$, never $0$.
-- source:
--   Harris (Ann. Probab. 2, 1974), Remark 7.12, p. 982

import Mathlib
import Definitions.Def_HarrisContact_Extinction_Model
open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HarrisContact.MeanSize

/-- Harris (Ann. Probab. 2, 1974), Remark 7.12, p. 982: under the conditions of Theorem 7.6,
`lim_{t → ∞} m_t(ξ) = 0` for every finite `ξ`. -/
theorem remark_7_12 {d : ℕ} (hd : 1 ≤ d) (μ : ℝ) (lam : ℕ → ℝ) (hμ : 0 < μ) (h0 : lam 0 = 0)
    (hlam : ∀ k, k ≤ 2 * d → 0 ≤ lam k)
    (hsub : ∀ k : ℕ, 1 ≤ k → k ≤ 2 * d → lam k / μ < k / (2 * (d : ℝ) - 1)) :
    ∀ ξ : HarrisContact.Extinction.Config d, Tendsto (fun t : ℝ => HarrisContact.Extinction.meanSize μ lam t ξ) atTop (𝓝 0) := by sorry
end HarrisContact.MeanSize
