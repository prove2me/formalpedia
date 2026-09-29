-- Prove2me | Theorems.Thm_FourExp_zero_count_arith
-- name    : FourExp.zero_count_arith
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-15T03:45:35.756372+00:00
-- url     : https://prove2.me/theorems/52059e8b-dd9e-404c-ab6e-cd03a25e3a57
-- title:
--   From the rescaled inequality to the zero count bound
-- statement:
--   **A real-variable inequality.**
--
--   Let $n \ge 2$, $x \ge 0$, $\lambda > 0$ and $\sigma \ge 0$ be real, with $n$ an integer. Suppose that for every $R > x + 1$,
--   $$\sigma\,\log\frac{R-x}{x+1} \le \log\Bigl(n!\,2^{n+1}\frac{R}{R-1}\Bigr) + 2R .$$
--   Then
--   $$\sigma < \frac{n}{\lambda} + 2\,\frac{1 + n^{\lambda}}{\lambda\log n}\,(1 + x).$$
--
--   **Why it should hold.** With $\Lambda = n^{\lambda}(1+x) + x$, taking $R = \Lambda$ gives $\log\frac{R-x}{x+1} = \lambda\log n$ and $2R = 2(1+n^\lambda)(1+x) - 2$. The claim then reduces to $\log(n!\,2^{n+1}) + \log\frac{\Lambda}{\Lambda - 1} < n\log n + 2$. That holds for $n \ge 6$ whenever $\Lambda \ge 3/2$. When $\Lambda < 3/2$ one has $x < 1/4$ and $n^\lambda < 3/2$, and $R = \tfrac{13}{4}x + \tfrac94$ works for every $n \ge 2$.
--
--   **A known gap in the source.** For $2 \le n \le 5$ with $\Lambda \ge 3/2$, the choice $R = \Lambda$ can fail. The 1971 derivation uses $n!\,2^n \le n^n$, which is false for $n \le 5. A numerical check suggests the statement still holds there with a better choice of $R$. It takes the best $R$ over $n = 2, \dots, 30$ and $n = 50, \dots, 10^5$, and $x \in [0, 1000]$; the tightest margin is about $0.24$, at $n = 2$, $x = 0$. A proof must treat those cases explicitly.
--
--   **What it is for.** Together with `FourExp.expPoly_zero_count_scaled` it yields `FourExp.expPoly_zero_count`.
-- source:
--   Arithmetic step after M. Waldschmidt, Indépendance algébrique des valeurs de la fonction exponentielle, Bull. Soc. Math. France 99 (1971), 285–304, §4, (4.14). The paper's own derivation bounds n!·2ⁿ by nⁿ, which fails for n ≤ 5, so the argument must choose R more carefully for small n.

import Mathlib

namespace FourExp

theorem zero_count_arith
    (n : ℕ) (hn : 2 ≤ n) (x lam : ℝ) (hx : 0 ≤ x) (hlam : 0 < lam) (σ : ℝ) (hσ : 0 ≤ σ)
    (h : ∀ R : ℝ, x + 1 < R →
      σ * Real.log ((R - x) / (x + 1)) ≤ Real.log ((n.factorial : ℝ) * 2 ^ (n + 1) * R / (R - 1)) + 2 * R) :
    σ < (n : ℝ) / lam + 2 * (1 + (n : ℝ) ^ lam) / (lam * Real.log (n : ℝ)) * (1 + x) := by
  sorry

end FourExp
