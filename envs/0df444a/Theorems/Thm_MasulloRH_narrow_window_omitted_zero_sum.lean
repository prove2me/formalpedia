-- Prove2me | Theorems.Thm_MasulloRH_narrow_window_omitted_zero_sum
-- name    : MasulloRH.narrow_window_omitted_zero_sum
-- status  : Open
-- author  : @Yi
-- created : 2026-11-20T22:22:38.327255+00:00
-- url     : https://prove2.me/theorems/6d631fe7-ce53-4f51-b660-706b2183ed5d
-- title:
--   Open obstruction: vanishing of the omitted zero distribution in a strict positive window
-- statement:
--   For every strictly positive window of half-width less than one half, consider the nontrivial zeta zeros on or outside its boundary. The conjectured identity says that the multiplicity-weighted sum of the shifted Mellin transform over those zeros vanishes for every smooth compactly supported test in the positive reals with value zero at one. Absolute convergence follows from the full explicit formula. Vanishing is the independent spectral assertion needed to recover the restricted trace. RH implies it by making the omitted set empty. At widths at least one half no zeros of the open critical strip can be omitted.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 12.5.1.1, pp. 519–520, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Derived residual condition from comparison with the full-zero Weil formula. This is a proposed open consequence of the restricted trace assertion, not a separate theorem established in the draft.

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
open MeasureTheory Set MasulloRH ConnesRZ

theorem MasulloRH.narrow_window_omitted_zero_sum (α : ℝ) (hα : 0 < α) (hsmall : α < 1/2)
    (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := by sorry
