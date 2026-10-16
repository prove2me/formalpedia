-- Prove2me | Theorems.Thm_JRPHard_Shor_window_chain
-- name    : JRPHard.Shor.window_chain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T12:37:37.145361+00:00
-- url     : https://prove2.me/theorems/61907557-8a19-4776-bdb8-ce4fee03d426
-- title:
--   Appendix, p. 16 — chain of prime windows
-- statement:
--   Let $n\ge1$, let $b,c,\lambda,P$ be real, and suppose $0<\lambda\le2n$, $cb<\lambda2^{b/2}/(4n)$, and
--   $$2^b-cb2^{b/2}<P<2^b+cb2^{b/2}.$$
--   Then both subsequent bounds in the Appendix hold:
--   $$2^b\left(1-\frac{\lambda}{4n}\right)<P<2^b\left(1+\frac{\lambda}{4n}\right),$$
--   $$2^b2^{-\lambda/(2n)}<P<2^b2^{\lambda/(2n)}.$$
--   This transfers the sampled prime window into bounds that multiply over any index subset. The condition $\lambda\le2n$ records the domain of the printed inequality $2^{-x}\le1-x/2$.
-- source:
--   Schulz and Telha, Integer factorization and Riemann's hypothesis: Why two-item joint replenishment is hard, arXiv:2007.09045v1, p. 16, Appendix, three displayed window inequalities

import Mathlib

namespace JRPHard.Shor

/-- Appendix, p. 16: the two successive window bounds for a sampled prime. -/
theorem window_chain (n : ℕ) (hn : 0 < n) (b c lam P : ℝ)
    (hlam0 : 0 < lam) (hlam : lam ≤ 2 * (n : ℝ))
    (hc : c * b < lam * (2 : ℝ) ^ (b / 2) / (4 * (n : ℝ)))
    (hwin : (2 : ℝ) ^ b - c * b * (2 : ℝ) ^ (b / 2) < P ∧
      P < (2 : ℝ) ^ b + c * b * (2 : ℝ) ^ (b / 2)) :
    ((2 : ℝ) ^ b * (1 - lam / (4 * (n : ℝ))) < P ∧
      P < (2 : ℝ) ^ b * (1 + lam / (4 * (n : ℝ)))) ∧
    ((2 : ℝ) ^ b * (2 : ℝ) ^ (-(lam / (2 * (n : ℝ)))) < P ∧
      P < (2 : ℝ) ^ b * (2 : ℝ) ^ (lam / (2 * (n : ℝ)))) := by sorry

end JRPHard.Shor
