-- Prove2me | Theorems.Thm_MasulloRH_single_resolvent_test
-- name    : MasulloRH.single_resolvent_test
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-20T22:41:16.429566+00:00
-- url     : https://prove2.me/theorems/0a35acdb-fbbc-407f-a9ce-f3f660e29b8d
-- title:
--   A single real resolvent detects every zero omitted by the Masullo window
-- statement:
--   For any centered window of real half-width $\alpha$, evaluate the regularized trace expression and the full-strip expression at the single real argument $s=3$, using the common subtraction point $5/2$. The real part of the narrow expression is at least that of the full expression if and only if every actual nontrivial zeta zero lies strictly inside the window. This is a one-sided scalar criterion, valid even for a zero on the boundary. It uses the unconditional low-height zero-free rectangle to make each omitted summand strictly positive, and it does not assume a vanishing assertion or RH.
-- source:
--   Derived from the rational reconstruction of Masullo, The Music of the Primes, §§1.4.2–1.4.5, pp. 28–30, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, and the proved platform results MasulloRH.weighted_zero_summability and ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six.

import Definitions.Def_MasulloRH_RegularizedTrace
open MasulloRH

theorem MasulloRH.single_resolvent_test (α : ℝ) :
    (regularizedTraceRHS (1/2) 3).re ≤ (regularizedTraceRHS α 3).re ↔
      ∀ ρ : ZetaZerosInTraceStrip (1/2), |ρ.val.re - 1/2| < α := by sorry
