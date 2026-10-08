-- Prove2me | Theorems.Thm_KalaiVempala_Multiplicative_expected_sup_norm_laplace
-- name    : KalaiVempala.Multiplicative.expected_sup_norm_laplace
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:52:47.018146+00:00
-- url     : https://prove2.me/theorems/42530ac8-445d-43b0-8fe2-6dfb5c44db32
-- title:
--   Pp. 299, 303 — under dμ ∝ e^{−ε|x|₁}, E|p|_∞ ≤ (1 + ln n)/ε
-- statement:
--   Let $\varepsilon > 0$ and let $p$ be drawn from the FPL\* perturbation law $\mu_\varepsilon$ on $\mathbb R^n$, with density $(\varepsilon/2)^n e^{-\varepsilon |x|_1}$. Then
--   $$\mathbb E_{p\sim\mu_\varepsilon}\big[\,|p|_\infty\big] \;\le\; \frac{1 + \ln n}{\varepsilon}.$$
--
--   Under $\mu_\varepsilon$ the absolute values $|p_i|$ are independent exponential variables with rate $\varepsilon$, so $|p|_\infty$ is $1/\varepsilon$ times a maximum of $n$ standard exponentials. The paper states this at the end of §2 ("for scaled exponential distributions, the expected maximum is at most $(1 + \ln n)/\varepsilon$", p. 299) and uses it in the proof of Theorem 1.1(b) (p. 303).
--
--   **Formalization Note** $|p|_\infty$ is the Lean norm `‖p‖` on `Fin n → ℝ` (the sup norm). The page writes "exponential distributions with mean $\varepsilon$" and "$|p_1|_\infty \le (1+\ln n)/\varepsilon$"; the distributions have rate $\varepsilon$ (mean $1/\varepsilon$), and the bound is on the expectation. Both are corrected here. No hypothesis on $n$ is needed: for $n = 0$ both $|p|_\infty$ and $\ln 0$ are $0$ in Lean and the bound reads $0 \le 1/\varepsilon$. The integrand is integrable ($|p|_\infty \le |p|_1$).
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 303, proof of Theorem 1.1(b) (citing the end of §2, p. 299)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem expected_sup_norm_laplace (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∫ p, ‖p‖ ∂(laplaceLaw n ε) ≤ (1 + Real.log n) / ε := by sorry

end KalaiVempala.Multiplicative
