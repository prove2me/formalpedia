-- Prove2me | Theorems.Thm_MasulloAudit_printed_archimedean_gamma_integral_diverges
-- name    : MasulloAudit.printed_archimedean_gamma_integral_diverges
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T04:11:21.919262+00:00
-- url     : https://prove2.me/theorems/2f5f2b93-f3f2-4784-9a51-028cce7a5b16
-- title:
--   The upper tail of the printed real gamma integral diverges
-- statement:
--   In the real-place, trivial-character specialization of (B.4.2.15), write $h(t)=\phi(e^t)$. The printed integrand has the form
--   $$G(t)=\frac{h(0)}{t}-(h(t)+h(-t))K(t)$$
--   with the displayed kernel $K$. For every smooth compactly supported real $h$ with $h(0)>0$, there is $R>0$ such that for all $B\ge R$,
--   $$\int_R^B G(t)\,dt=h(0)\log(B/R).$$
--   The upper improper integral therefore diverges to $+\infty$. The formal statement leaves the factor $K$ arbitrary because its coefficient is identically zero on this tail.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, p. 616, Proposition B.4.2.1 and Eq. (B.4.2.15), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf#page=616. The same undamped subtraction appears in the archimedean term of (B.4.2.17).

import Mathlib

open MeasureTheory

theorem MasulloAudit.printed_archimedean_gamma_integral_diverges (h : SchwartzMap ℝ ℝ) (hC : HasCompactSupport h) (h0 : 0 < h 0) (K : ℝ → ℝ) :
    let f := fun t : ℝ ↦ h 0/t-(h t+h (-t))*K t
    ∃ R > (0:ℝ), (∀ B ≥ R, (∫ t in R..B, f t) = h 0*Real.log (B/R)) ∧
      Filter.Tendsto (fun B : ℝ ↦ ∫ t in R..B, f t) Filter.atTop Filter.atTop ∧
      ¬IntegrableOn f (Set.Ioi (0:ℝ)) := by sorry
