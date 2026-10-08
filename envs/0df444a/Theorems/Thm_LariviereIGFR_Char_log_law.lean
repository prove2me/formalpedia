-- Prove2me | Theorems.Thm_LariviereIGFR_Char_log_law
-- name    : LariviereIGFR.Char.log_law
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T09:38:32.304365+00:00
-- url     : https://prove2.me/theorems/a3787325-365f-43e6-b5d8-31c21129c36b
-- title:
--   Proof of Theorem 1, p. 603 — Φ̄_L(ξ) = Φ̄(e^ξ) and φ_L(ξ) = e^ξφ(e^ξ) for X_L = log X
-- statement:
--   Let $X \ge 0$ have law $\mu$ with distribution function $\Phi$ and regular density $\varphi$, and let $X_L = \log X$, with distribution function $\Phi_L$. Then for every real $\xi$,
--   $$\Phi_L(\xi) = \Phi(e^{\xi}), \qquad\text{equivalently}\qquad \bar\Phi_L(\xi) = \bar\Phi(e^{\xi}),$$
--   and
--   $$\varphi_L(\xi) = e^{\xi}\varphi(e^{\xi})$$
--   is a regular density of $X_L$: it is a density of the law of $\log X$, it is the derivative of $\Phi_L$ on the support of $X_L$, and it vanishes where $\Phi_L = 0$.
--
--   This change of variables is the first step of the proof of Theorem 1: it transports every statement about $X_L$ back to $X$.
--
--   **Formalization Note** The law of $X_L$ is the image measure of $\mu$ under `Real.log`, which is measurable, so the image is a genuine probability measure. Lean sets $\log 0 = 0$ and $\log x = \log|x|$; these junk values do not matter because $\mu$ gives no mass to $(-\infty, 0]$ ($X \ge 0$, and $\{0\}$ is null since $\mu$ has a density).
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §2, proof of Theorem 1, first sentence

import Mathlib
import Definitions.Def_LariviereIGFR_Char_Setting

namespace LariviereIGFR.Char

open MeasureTheory ProbabilityTheory

theorem log_law (μ : Measure ℝ) [IsProbabilityMeasure μ] (φ : ℝ → ℝ)
    (hnn : μ (Set.Iio 0) = 0) (hφ : IsRegDensity μ φ) :
    (∀ ξ : ℝ, cdf (μ.map Real.log) ξ = cdf μ (Real.exp ξ)) ∧
      IsRegDensity (μ.map Real.log) (fun ξ => Real.exp ξ * φ (Real.exp ξ)) := by sorry

end LariviereIGFR.Char
