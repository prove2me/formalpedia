-- Prove2me | Theorems.Thm_NAGFlow_GradCorr_alpha0_bound
-- name    : NAGFlow.GradCorr.alpha0_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T16:29:52.828082+00:00
-- url     : https://prove2.me/theorems/8aa0e1f1-20de-44cd-a0a9-05b75578b113
-- title:
--   Proof of Theorem 5.1, p. 21 — Lα₀² = γ₀(1 + α₀) gives α₀ = (γ₀ + √(4γ₀L + γ₀²))/(2L) and 1/(1 + α₀) ≤ L/γ₀
-- statement:
--   Let $L>0$, $\gamma_0>0$ and $\alpha_0>0$ satisfy $L\alpha_0^2=\gamma_0(1+\alpha_0)$. Then
--   $$\alpha_0=\frac{1}{2L}\left(\gamma_0+\sqrt{4\gamma_0L+\gamma_0^2}\right),$$
--   and
--   $$\frac{1}{1+\alpha_0}=\frac{2L}{\gamma_0+2L+\sqrt{4\gamma_0L+\gamma_0^2}}\le\frac{L}{\gamma_0}.$$
--
--   The bound converts the factor $\mathcal L_0/(1+\alpha_0)$ into the constant $C_{\gamma_0,L}$ of (89) in the proof of the rate (88). Theorem 5.2 inherits this step from the proof of Theorem 5.1, since it uses the same step sizes.
-- source:
--   Luo & Chen, arXiv:1909.03145v4, proof of Theorem 5.1, displays after (90), p. 21 (cited by the proof of Theorem 5.2, p. 22)

import Mathlib

namespace NAGFlow.GradCorr

/-- The bound on `1/(1 + α₀)` in the proof of Theorem 5.1 (Luo & Chen, arXiv:1909.03145v4, p. 21).
If `L > 0`, `γ₀ > 0` and `α₀ > 0` satisfy `Lα₀² = γ₀(1 + α₀)`, then
`α₀ = (γ₀ + √(4γ₀L + γ₀²))/(2L)` and `1/(1 + α₀) = 2L/(γ₀ + 2L + √(4γ₀L + γ₀²)) ≤ L/γ₀`. -/
theorem alpha0_bound (L γ0 α0 : ℝ) (hL : 0 < L) (hγ0 : 0 < γ0) (hα0 : 0 < α0)
    (hrel : L * α0 ^ 2 = γ0 * (1 + α0)) :
    α0 = (γ0 + Real.sqrt (4 * γ0 * L + γ0 ^ 2)) / (2 * L) ∧
      1 / (1 + α0) = 2 * L / (γ0 + 2 * L + Real.sqrt (4 * γ0 * L + γ0 ^ 2)) ∧
      1 / (1 + α0) ≤ L / γ0 := by sorry

end NAGFlow.GradCorr
