-- Prove2me | Theorems.Thm_FreedmanTail_Bernstein_lemma_3_1
-- name    : FreedmanTail.Bernstein.lemma_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:31:48.427822+00:00
-- url     : https://prove2.me/theorems/45f7d003-a213-4423-bb96-238890f6d67c
-- title:
--   (3.1) Lemma — g(x) = (e^x − 1 − x)/x², g(0) = ½, is increasing
-- statement:
--   Define $g:\mathbb R\to\mathbb R$ by $g(0)=\tfrac12$ and
--   $$g(x)=\frac{e^{x}-1-x}{x^{2}}\qquad(x\neq0).$$
--   Then $g$ is strictly increasing: $x<y$ implies $g(x)<g(y)$.
--
--   The value $g(0)=\tfrac12$ is the limit of the quotient at $0$, so $g$ is continuous. Monotonicity of $g$ is the analytic fact behind Corollary (3.2) and hence behind every exponential upper bound of the paper.
--
--   **Formalization Note** The page says "$g$ is increasing", and its proof shows $g'(x)>0$ for $x\neq0$; the statement is the strict monotonicity this establishes.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 106 (PDF p. 7), (3.1) Lemma

import Mathlib

namespace FreedmanTail.Bernstein

/-- Freedman (1975), (3.1) Lemma, p. 106: `g(0) = 1/2`, `g(x) = (e^x − 1 − x)/x²` for `x ≠ 0`
is (strictly) increasing. -/
theorem lemma_3_1 :
    StrictMono (fun x : ℝ => if x = 0 then (1 / 2 : ℝ) else (Real.exp x - 1 - x) / x ^ 2) := by sorry

end FreedmanTail.Bernstein
