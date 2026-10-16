-- Prove2me | Theorems.Thm_NeedPersuasion_Homog_betaFi_lower_bound
-- name    : NeedPersuasion.Homog.betaFi_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T01:04:21.684015+00:00
-- url     : https://prove2.me/theorems/90d00166-b5ad-4111-9794-6f9055170ac3
-- title:
--   App. C, proof of Proposition 1, p. 40 — β_fi ≥ 1 − 1/(m_fi + 1) for all λ_L ≤ 1
-- statement:
--   Let $0 < \lambda_L \le 1$ and $m \in \mathbb N_0$. Then
--   $$\frac{\sum_{n=0}^{m-1}\lambda_L^n}{\sum_{n=0}^{m}\lambda_L^n} \;\ge\; 1 - \frac{1}{m+1}.$$
--
--   With $m = m_{fi}$ the left side is the constant $\beta_{fi}$ of Proposition 1, so the guarantee of full information approaches the optimum as the full-information threshold grows, uniformly in the arrival rate.
--
--   **Formalization Note** The statement is posed for an arbitrary $m$ instead of $m_{fi}$, which is a stronger statement; for $m = 0$ both sides are $0$.
-- source:
--   arXiv:2005.07253v3, App. C, proof of Proposition 1, p. 40, last sentence

import Mathlib

namespace NeedPersuasion.Homog

theorem betaFi_lower_bound (lamL : ℝ) (m : ℕ) (h0 : 0 < lamL) (h1 : lamL ≤ 1) :
    1 - 1 / ((m : ℝ) + 1) ≤
      (∑ n ∈ Finset.range m, lamL ^ n) / (∑ n ∈ Finset.range (m + 1), lamL ^ n) := by sorry

end NeedPersuasion.Homog
