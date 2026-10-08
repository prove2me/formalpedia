-- Prove2me | Theorems.Thm_L0BnB_BigMvsPR_lemma_1
-- name    : L0BnB.BigMvsPR.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:30:17.685409+00:00
-- url     : https://prove2.me/theorems/21321c86-0bf5-425b-867a-7b07bda7b117
-- title:
--   Lemma 1 — $t(\beta_i) \ge 0$ on $[-M, M]$ for $M \ge \sqrt{\lambda_0/\lambda_2}$
-- statement:
--   Let $\lambda_0, \lambda_2, M > 0$ and let $t(b) = 2\lambda_0\mathcal B(b\sqrt{\lambda_2/\lambda_0}) - \frac{\lambda_0}{M}|b| - \lambda_2 b^2$, where $\mathcal B$ is the reverse Huber penalty (4). If $M \ge \sqrt{\lambda_0/\lambda_2}$, then for every $b \in [-M, M]$,
--
--   $$t(b) \ge 0.$$
--
--   This is the coordinatewise inequality behind (11): for a loose Big-M bound, the $\mathrm{PR}(\infty)$ penalty $\psi_1$ dominates the Big-M coordinate penalty on the box.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 29, App. A, Lemma 1

import Mathlib
import Definitions.Def_L0BnB_BigMvsPR_Penalties
import Definitions.Def_L0BnB_BigMvsPR_Relaxations

namespace L0BnB.BigMvsPR

/-- Lemma 1, p. 29: if `M ≥ √(λ₀/λ₂)`, then `t(b) ≥ 0` for every `b ∈ [−M, M]`. -/
theorem lemma_1 (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hMlarge : Real.sqrt (lam0 / lam2) ≤ M) :
    ∀ b : ℝ, -M ≤ b → b ≤ M → 0 ≤ tGap lam0 lam2 M b := by sorry

end L0BnB.BigMvsPR
