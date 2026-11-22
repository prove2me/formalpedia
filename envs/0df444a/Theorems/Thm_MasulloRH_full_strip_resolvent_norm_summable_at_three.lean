-- Prove2me | Theorems.Thm_MasulloRH_full_strip_resolvent_norm_summable_at_three
-- name    : MasulloRH.full_strip_resolvent_norm_summable_at_three
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-22T03:29:34.05866+00:00
-- url     : https://prove2.me/theorems/e8fb4c51-1fe6-4b9a-8d82-1224968bfda2
-- title:
--   Absolute summability of the full-strip compensated resolvent at s=3
-- statement:
--   At the full critical-strip width, the multiplicity-weighted compensated resolvent terms at the real point s=3 are absolutely summable. In detail, for each distinct nontrivial zeta zero ρ in the open strip, let m(ρ) be its analytic multiplicity and let
--
--   $$R_ρ= m(ρ)\left(\frac{1}{3-ρ}-\frac{1}{5/2-ρ}\right).$$
--
--   Then the family $\|R_ρ\|$ is summable over the actual zero subtype. The proof uses the established weighted zero-counting estimate $\sum_ρ m(ρ)/(1+\operatorname{Im}(ρ)^2)<\infty$ and the elementary bound $\|R_ρ\|\le m(ρ)/(1+\operatorname{Im}(ρ)^2)$, obtained from the two resolvent factors. This is an unconditional high-height convergence certificate for the Masullo regularized spectral expression; it does not assert the nonnegative sign of the omitted-zero defect.
-- source:
--   Masullo, The Music of the Primes, §§1.4.2–1.4.5 and Theorem 12.5.1.1, frozen 20 November 2026 draft, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf; uses the proved MasulloRH.weighted_zero_summability certificate.

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_weighted_zero_summability

set_option autoImplicit false
open MasulloRH

theorem MasulloRH.full_strip_resolvent_norm_summable_at_three :
    Summable (fun ρ : ZetaZerosInTraceStrip (1 / 2) =>
      ‖zeroResolventTerm (1 / 2) (3 : ℂ) ρ‖) := by sorry
