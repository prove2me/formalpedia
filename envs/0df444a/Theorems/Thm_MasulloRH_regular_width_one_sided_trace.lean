-- Prove2me | Theorems.Thm_MasulloRH_regular_width_one_sided_trace
-- name    : MasulloRH.regular_width_one_sided_trace
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T00:42:45.746674+00:00
-- url     : https://prove2.me/theorems/e13a690e-b913-439b-846a-b573e79a4ccb
-- title:
--   The one-sided rational trace identity when neither strip boundary contains a zeta zero
-- statement:
--   For a positive half-width $\beta$ assume that neither of the lines $\Re(s)=1/2\pm\beta$ contains a nontrivial zeta zero. For smooth admissible rational norm tests whose closed support is contained in $(1,\infty)$, the real and finite-place contributions equal the two polar Mellin values less the zero sum in this strip.
--
--   These hypotheses align the support condition of Theorem 11.3.2.1 with widths where the endpoint multiplicity convention of (10.3.2.4) has no effect. This remains a spectral–geometric matching obligation in the proposed proof. The unconditional full-strip explicit formula alone does not establish the identity for all such widths.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 10.3.2.1, (10.3.2.3)–(10.3.2.4), Theorem 11.3.2.1, and Theorem 12.5.1.1, pp. 519–520. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RationalTrace

open MasulloRH MeasureTheory Set Filter Topology

theorem MasulloRH.regular_width_one_sided_trace (β : ℝ) (hβ : 0 < β)
    (hreg : ∀ ρ : ZetaZerosInTraceStrip (1/2), |ρ.val.re - 1/2| ≠ β)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) (hpos : tsupport φ ⊆ Ioi 1) :
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1/2) + mellin φ (-1/2) - ∑' ρ : ZetaZerosInTraceStrip β, zetaTraceTerm φ β ρ := by sorry
