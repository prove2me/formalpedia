-- Prove2me | Theorems.Thm_MasulloRH_trace_window_comparison
-- name    : MasulloRH.trace_window_comparison
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-20T22:17:04.14752+00:00
-- url     : https://prove2.me/theorems/49251e54-b1ef-4313-9a30-285f84fc789c
-- title:
--   Full explicit formula split into the strict Masullo window and its complement
-- statement:
--   For every smooth test function compactly supported in the positive reals with $\varphi(1)=0$, the real-place integrand is integrable, the prime-power series is summable, and both parts of the multiplicity-weighted zero series are summable. Split the full critical strip at the strict window $|\Re\rho-1/2|<\alpha$, putting both edges in the complement. Then the prime sum plus the two zero sums equals the two polar Mellin values plus the archimedean term of the Weil explicit formula evaluated at $g(x)=\varphi(e^x)$.
--
--   This comparison holds for every real width. It tracks the omitted spectral contribution explicitly, including when the width is zero. The separate identification of the archimedean term with the physical real-place integral and the question of cancellation of the omitted sum are left visible.
-- source:
--   Derived comparison of the rational normalization in A. M. Masullo, The Music of the Primes, Theorem 12.5.1.1, pp. 519–520 (20 November 2026 draft), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, with the full-zero Weil explicit formula as formalized by ConnesRZ.explicit_formula on Prove2Me. The split identity is a derived result.

import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_ConnesRZ_weil_defs
open MeasureTheory MasulloRH Set

theorem MasulloRH.trace_window_comparison (α : ℝ) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ) :
    let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧ Summable (primePowerTraceTerm φ) ∧
    Summable (zetaTraceTerm φ α) ∧
    Summable (fun r : omitted => (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) ∧
    (∑' i, primePowerTraceTerm φ i) + (∑' ρ, zetaTraceTerm φ α ρ) +
      (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) =
    mellin φ (1/2) + mellin φ (-1/2) + ConnesRZ.archTerm (φ ∘ Real.exp) := by sorry
