-- Prove2me | Theorems.Thm_NoisyPrototyping_ReservationPolicy_footnote_4
-- name    : NoisyPrototyping.ReservationPolicy.footnote_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T23:03:48.767734+00:00
-- url     : https://prove2.me/theorems/788a41f6-f4b1-4910-800a-f63824ccc1bd
-- title:
--   Footnote 4, p. 10 — the fidelity-adjusted reservation price exists: E[max{0, X − R}] is non-increasing in R and the equation has a least root
-- statement:
--   Let $G$ be a probability distribution on $\mathbb R$ with finite mean, let $X \sim G$, and let $w > 0$. Then:
--
--   1. for every $R$, $\;E[\max\{R, X\}] - R = E[\max\{0, X - R\}]$;
--   2. the function $R \mapsto E[\max\{0, X - R\}]$ is non-increasing;
--   3. every value in $(0, \infty)$ is attained by this function;
--   4. the equation
--   $$E[\max\{0, X - R\}] = w$$
--   has a smallest solution $R$.
--
--   With $X = X_i \sim g_i$ and $w = w_i$, the smallest solution is the fidelity-adjusted reservation price $R_i$ of prototype $i$ (p. 10). The statement justifies that $R_i$ is well defined.
--
--   **Formalization Note** The footnote says the function "has the range $(0, \infty)$". Read literally that is false when $X$ is bounded above, because the function then vanishes beyond the essential supremum and its range is $[0, \infty)$. What holds in general, and what the existence argument uses, is that every value in $(0, \infty)$ is attained (item 3). The footnote writes $Y_i$ for $X_i$.
-- source:
--   Bhaskaran and Erat, Optimal Prototyping with Noisy Measurements, author manuscript of 6 Nov 2024 (MSOM 2025, doi:10.1287/msom.2024.1133), p. 10, definition of R_i and footnote 4 (repeated as footnote 12, p. A2 (PDF 33))

import Mathlib
import Definitions.Def_NoisyPrototyping_ReservationPolicy_Model

namespace NoisyPrototyping.ReservationPolicy
open MeasureTheory
theorem footnote_4 (G : Measure ℝ) [IsProbabilityMeasure G]
    (hG : Integrable (fun x : ℝ => x) G) (w : ℝ) (hw : 0 < w) :
    (∀ r : ℝ, (∫ x, max r x ∂G) - r = ∫ x, max (x - r) 0 ∂G) ∧
    Antitone (fun r : ℝ => ∫ x, max (x - r) 0 ∂G) ∧
    Set.Ioi (0 : ℝ) ⊆ Set.range (fun r : ℝ => ∫ x, max (x - r) 0 ∂G) ∧
    ∃ R : ℝ, IsLeast {r : ℝ | ∫ x, max (x - r) 0 ∂G = w} R := by sorry
end NoisyPrototyping.ReservationPolicy
