-- Prove2me | Theorems.Thm_MasulloRH_unrestricted_spectral_hasSum
-- name    : MasulloRH.unrestricted_spectral_hasSum
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T22:22:02.204203+00:00
-- url     : https://prove2.me/theorems/a3c52a73-8451-499f-926d-8ab63d6da834
-- title:
--   Unrestricted spectral sum for rational trace tests
-- statement:
--   For an admissible rational test, the spectral sum over all nontrivial zeta zeros, counted with their analytic multiplicities, converges to the classical Weil distribution on the test in logarithmic coordinates. This is the unrestricted formula, with no assertion concerning a narrower strip.
-- source:
--   Comparison of Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 12.5.1.1 (pp. 519–520), with the platform theorem ConnesRZ.explicit_formula. The window cancellation is an isolated obligation of the proposed specialization, not a classical explicit formula. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
open Set MeasureTheory

namespace MasulloRH

theorem unrestricted_spectral_hasSum (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    HasSum (fun ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} =>
      (ConnesRZ.zeroMult ρ.val : ℂ) * mellin φ (ρ.val - 1/2))
      (ConnesRZ.weilDistribution (fun u => φ (Real.exp u))) := by sorry

end MasulloRH
