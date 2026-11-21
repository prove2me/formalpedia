-- Prove2me | Theorems.Thm_MasulloRH_window_trace_boundary_limits
-- name    : MasulloRH.window_trace_boundary_limits
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T00:42:45.382141+00:00
-- url     : https://prove2.me/theorems/d5435182-7366-4772-be76-08b3edf5d4ca
-- title:
--   One-sided limits of boundary-capped zeta traces and the exact edge contribution
-- statement:
--   Let $b_n\to\alpha$ be a sequence of real half-widths. Sum the usual shifted Mellin values of an admissible rational test over nontrivial zeros in the closed window of half-width $b_n$, using full multiplicity in its interior and multiplicity capped at an arbitrary nonnegative integer $c_n$ on its two edges. Approaching from smaller widths gives the strict-window trace at $\alpha$. Approaching from larger widths gives the strict-window trace plus the complete contribution from both edges, with full analytic multiplicity. No zero-location or spacing assumption is needed. This makes precise the difference between the closed windows in (10.3.2.3) and the interior window in (12.5.1.3).
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 10.3.2.1, (10.3.2.3)–(10.3.2.4), Theorem 11.3.2.1, and Theorem 12.5.1.1, pp. 519–520. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RationalTrace

open MasulloRH MeasureTheory Set Filter Topology

theorem MasulloRH.window_trace_boundary_limits (α : ℝ) (b : ℕ → ℝ)
    (hb : Tendsto b atTop (𝓝 α)) (c : ℕ → ℕ) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let F := fun n : ℕ => ∑' ρ : ZetaZerosInTraceStrip (1/2),
      if |ρ.val.re-1/2| < b n then zetaTraceTerm φ (1/2) ρ
      else if |ρ.val.re-1/2| = b n then
        ((min (analyticOrderNatAt riemannZeta ρ.val) (c n) : ℕ) : ℂ) * mellin φ (ρ.val-1/2)
      else 0
    ((∀ n, b n < α) → Tendsto F atTop (𝓝 (∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ))) ∧
    ((∀ n, α < b n) → Tendsto F atTop (𝓝 ((∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ) +
      ∑' ρ : {z : ZetaZerosInTraceStrip (1/2) // |z.val.re-1/2| = α}, zetaTraceTerm φ (1/2) ρ.val))) := by sorry
