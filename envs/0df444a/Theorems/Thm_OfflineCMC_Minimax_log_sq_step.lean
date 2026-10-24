-- Prove2me | Theorems.Thm_OfflineCMC_Minimax_log_sq_step
-- name    : OfflineCMC.Minimax.log_sq_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T04:37:01.681+00:00
-- url     : https://prove2.me/theorems/2fbf8fe0-1242-4280-8418-da31687fcf1b
-- title:
--   G.2, display after (G.16), p. 50 (corrected: the claim that f is decreasing is omitted) — f(x) < 2 for large x, and m ≥ 2x(log x)² ⇒ m/(log m)² ≥ x
-- statement:
--   Let
--   $$
--   f(x)=\Big(1+\frac{\log 2}{\log x}+2\,\frac{\log\log x}{\log x}\Big)^2 .
--   $$
--   Then:
--
--   1. there is a constant $c$ such that $f(x)<2$ for every $x>c$;
--   2. there is a constant $c>1$ such that for every $x>c$ and every real $m$,
--   $$
--   m\ge 2x(\log x)^2\quad\Longrightarrow\quad \frac{m}{(\log m)^2}\ge x .
--   $$
--
--   In the proof of Theorem 2 this is applied with $x=\mathbb C_{T,\delta}$ and $x=\mathbb C_{\zeta,\delta}$. It turns a sample size of order $x(\log x)^2$ into the inequality $m/(\log m)^2\ge x$ that the Bernstein bound of Proposition 3 needs.
--
--   Differences from the source:
--   - correction: "This is obviously decreasing in $x$" → not stated; reason: false. With $L=\log x$, the derivative of $\log2/L+2\log L/L$ is $(2-2\log L-\log2)/L^2$, which is positive for $L<e^{1-\log2/2}\approx1.92$, i.e. for $x<6.8$. The claim is not used.
--   - generalization: $m=2\mathbb C_{T,\delta}(\log\mathbb C_{T,\delta})^2$ → every $m\ge2x(\log x)^2$, for every $x>c$; reason: at $m=2x(\log x)^2$ this is the page's display with $x=\mathbb C_{T,\delta}$. It extends to larger $m$ because $m/(\log m)^2$ is increasing for $m\ge e^2$.
-- source:
--   Banerjee, Honnappa & Rao, Offline Estimation of Controlled Markov Chains: Minimaxity and Sample Complexity, arXiv:2211.07092v5, p. 50, App. G.2, display after (G.16)

import Mathlib

namespace OfflineCMC.Minimax

theorem log_sq_step :
    (∃ c : ℝ, ∀ x : ℝ, c < x →
      (1 + Real.log 2 / Real.log x + 2 * (Real.log (Real.log x) / Real.log x)) ^ 2 < 2) ∧
    ∃ c : ℝ, 1 < c ∧ ∀ x : ℝ, c < x → ∀ m : ℝ, 2 * x * Real.log x ^ 2 ≤ m →
      x ≤ m / Real.log m ^ 2 := by sorry

end OfflineCMC.Minimax
