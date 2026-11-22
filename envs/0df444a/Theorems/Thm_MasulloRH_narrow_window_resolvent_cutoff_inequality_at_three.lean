-- Prove2me | Theorems.Thm_MasulloRH_narrow_window_resolvent_cutoff_inequality_at_three
-- name    : MasulloRH.narrow_window_resolvent_cutoff_inequality_at_three
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-22T20:17:29.513137+00:00
-- url     : https://prove2.me/theorems/a9d43338-5497-4b4d-8df5-127550c8b1e6
-- title:
--   A cofinal one-sided narrow-window trace estimate at the real resolvent parameter 3
-- statement:
--   Let $0<\alpha<1/2$ and assume that no zero of the Riemann zeta function with positive imaginary part lies on $\Re s=1/2+\alpha$. Use the smooth compactly supported regularized trace tests at the single parameter $s=3$. The test with index $n$ inserts the cutoff `traceLogCutoff n` in the difference $t^{-5/2}-t^{-2}$ on $t>1$ and is zero for $t\leq1$.
--
--   Write $A_n$ and $P_n$ for the real-place and prime-power terms of this test, $B_n$ for the sum of its two polar Mellin terms, and $S_{\alpha,n}$ for its multiplicity-weighted Mellin sum over the nontrivial zeros with $|\Re \rho-1/2|<\alpha$. Show that for arbitrarily large cutoff indices $n$,
--   $$
--   \Re(B_n-S_{\alpha,n})\leq \Re(A_n+P_n).
--   $$
--   This asks for one direction of the geometric-to-spectral comparison on a fixed family of tests. The terms are the rational trace normalization of the mission and the cutoffs are its regularized reconstruction.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 28–30, §§1.4.2–1.4.5, and pp. 519–520, Theorem 12.5.1.1, equations (12.5.1.1)–(12.5.1.4). One-sided cofinal estimate obtained by restricting the claimed comparison to the mission’s reconstructed regularized cutoff tests at s = 3.

import Definitions.Def_MasulloRH_RegularizedTrace

open MasulloRH Filter
set_option autoImplicit false

theorem MasulloRH.narrow_window_resolvent_cutoff_inequality_at_three
    (α : ℝ) (hα : 0 < α) (hα2 : α < 1 / 2)
    (hBoundary : ∀ z : ℂ, riemannZeta z = 0 → z.re = 1 / 2 + α → 0 < z.im → False) :
    ∃ᶠ n : ℕ in atTop,
      (cutoffPolar n (3 : ℂ) - cutoffSpectral α n (3 : ℂ)).re ≤
        (cutoffArch n (3 : ℂ) + cutoffPrime n (3 : ℂ)).re := by sorry
