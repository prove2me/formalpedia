-- Prove2me | Theorems.Thm_MemoSDPI_Main_gaussian_tail_bounds
-- name    : MemoSDPI.Main.gaussian_tail_bounds
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:41:09.158204+00:00
-- url     : https://prove2.me/theorems/ddd2dcfe-bf77-4aca-a8e9-199e20207e86
-- title:
--   Gaussian tail bounds x/(1+x²) ϕ(x) ≤ Pr[g ≥ x] ≤ ϕ(x)/x for x > 0 (§4, proof of Theorem 4.2)
-- statement:
--   Let $g$ be a standard Gaussian random variable with density $\phi(x) = e^{-x^2/2}/\sqrt{2\pi}$. For every $x > 0$,
--   $$
--   \frac{x}{1+x^2}\,\phi(x) \;\le\; \Pr[g \ge x] \;\le\; \frac{\phi(x)}{x}.
--   $$
--   The proof of Theorem 4.2 uses the lower bound at $x = \sqrt{\ell}$ and the upper bound at $x = \sqrt{\ell}/2$ (cited from Polyanskiy–Wu, Exercise V.25, eq. (V.8)).
--
--   **Formalization Note** $\phi$ is Mathlib's `gaussianPDFReal 0 1` and $\Pr[g \ge x]$ is the real value of the standard Gaussian measure `gaussianReal 0 1` on $[x, \infty)$.
--
--   Differences from the source: none.
-- source:
--   Feldman, Lyu, Talwar, Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities, STOC 2027 submission (manuscript sha256 dbb300da…), p. 16, §4, proof of Theorem 4.2, Gaussian tail bounds

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace MemoSDPI.Main

/-- Feldman, Lyu, Talwar, *Lower Bounds for Memorization, Privacy and Replicability from Not-So-Strong Data Processing Inequalities*, STOC 2027 submission (manuscript sha256 dbb300da…), p. 16, proof of Theorem 4.2 (cited from [PW24, Exercise V.25, eq. (V.8)]): for a
standard Gaussian `g` and `x > 0`, `x/(1 + x²) · ϕ(x) ≤ Pr[g ≥ x] ≤ ϕ(x)/x`. -/
theorem gaussian_tail_bounds (x : ℝ) (hx : 0 < x) :
    x / (1 + x ^ 2) * gaussianPDFReal 0 1 x ≤ (gaussianReal 0 1).real (Set.Ici x) ∧
      (gaussianReal 0 1).real (Set.Ici x) ≤ gaussianPDFReal 0 1 x / x := by sorry

end MemoSDPI.Main
