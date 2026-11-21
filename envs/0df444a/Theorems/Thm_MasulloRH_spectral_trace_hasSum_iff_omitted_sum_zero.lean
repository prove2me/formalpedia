-- Prove2me | Theorems.Thm_MasulloRH_spectral_trace_hasSum_iff_omitted_sum_zero
-- name    : MasulloRH.spectral_trace_hasSum_iff_omitted_sum_zero
-- status  : Proved
-- author  : @dga471
-- created : 2026-11-20T23:21:47.407552+00:00
-- url     : https://prove2.me/theorems/0456a215-263d-405e-b942-1f72bace5a8e
-- title:
--   Trace window equivalence: the spectral HasSum holds iff the omitted zero sum vanishes
-- statement:
--   For every real window half-width $\alpha$ and every rational trace test function $\varphi$, the window spectral sum of the rational trace formula converges to its stated trace value — the two polar Mellin values minus the real-place integral and the prime-power sum — if and only if the multiplicity-weighted Mellin sum over the omitted critical zeros, those on or outside the window boundary $|\Re\rho - 1/2| \ge \alpha$, vanishes:
--
--   $$\sum_{|\Re\rho - 1/2| < \alpha} m_\rho\, \widehat\varphi(\rho) \;\text{has sum}\; \widehat\varphi(1/2) + \widehat\varphi(-1/2) - (\text{real place} + \text{prime powers}) \iff \sum_{|\Re\rho - 1/2| \ge \alpha} m_\rho\, \widehat\varphi(\rho) = 0.$$
--
--   Both directions are formal consequences of the proved window comparison identity (`MasulloRH.trace_window_comparison`) together with the identification of the archimedean term with the negative real-place integral (`MasulloRH.archTerm_log_test_eq_neg_real_place`); no new analytic input is involved. Note that no positivity hypothesis on $\alpha$ is needed: the comparison identity holds for every real $\alpha$, so the equivalence does too. The node isolates exactly what remains between the proved comparison theorem and the open spectral assertion `MasulloRH.spectral_trace_hasSum`: the single scalar condition that the omitted zero sum is zero.
-- source:
--   Derived equivalence from the proved theorems MasulloRH.trace_window_comparison (49251e54-b1ef-4313-9a30-285f84fc789c) and MasulloRH.archTerm_log_test_eq_neg_real_place (1bde7ef9-2ece-4f13-a2e8-d1044e2361c7), relating the open nodes MasulloRH.spectral_trace_hasSum (ab2befc9-2e68-45a1-9474-fcf930cb1338) and MasulloRH.narrow_window_omitted_zero_sum (6d631fe7-ce53-4f51-b660-706b2183ed5d). Underlying source: A. M. Masullo, The Music of the Primes, Theorem 12.5.1.1, pp. 519-520.

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
open MeasureTheory Set MasulloRH ConnesRZ

theorem MasulloRH.spectral_trace_hasSum_iff_omitted_sum_zero (α : ℝ) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ) :
    (HasSum (zetaTraceTerm φ α) ((mellin φ (1 / 2) + mellin φ (-1 / 2)) -
      ((∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) + ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i))
    ↔
    (let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
     (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0)) := by sorry
