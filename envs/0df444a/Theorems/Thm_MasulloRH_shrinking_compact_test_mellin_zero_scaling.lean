-- Prove2me | Theorems.Thm_MasulloRH_shrinking_compact_test_mellin_zero_scaling
-- name    : MasulloRH.shrinking_compact_test_mellin_zero_scaling
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:33:52.790175+00:00
-- url     : https://prove2.me/theorems/aaa585f9-603c-4d8e-836a-69eddb38e84e
-- title:
--   Leading logarithm of the shrinking Mellin spectral sum throughout the critical strip
-- statement:
--   Let $h$ be a smooth compactly supported real test on $\mathbb R$. For each nontrivial zeta zero $\rho=\beta+i\gamma$ of positive ordinate and multiplicity $m_\rho$, put
--   $$
--   M_\varepsilon(\rho)=\operatorname{Re}\int_{\mathbb R}
--         h(x)e^{\varepsilon(\rho-1/2)x}\,dx,\qquad
--   F(u)=\operatorname{Re}\widehat h(u)
--   $$
--   with the self-dual additive Fourier phase $e^{-2\pi i ux}$. For all sufficiently small $\varepsilon>0$, the positive-half spectral series is summable and satisfies
--   $$
--   2\varepsilon\sum_{\gamma>0} m_\rho M_\varepsilon(\rho)
--   =h(0)\log(1/\varepsilon)+O_h(1).
--   $$
--   Moreover,
--   $$
--   2\varepsilon\sum_{\gamma>0}m_\rho
--     \left(M_\varepsilon(\rho)-F(\varepsilon\gamma/(2\pi))\right)
--   \longrightarrow 0.
--   $$
--   Both sums use every positive nontrivial zero location with its full analytic multiplicity. The Fourier comparison uses the same ordinates, evaluating the Mellin exponent at their projections onto the critical line.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Chapter 13, Eq. (13.3.1.4), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Uses Prove2Me weighted positive-zero scaling b09a7d33 and the proved summability of zeroDecayWeight.

import Mathlib
import Definitions.Def_Zeta23_Statement

open MeasureTheory

theorem MasulloRH.shrinking_compact_test_mellin_zero_scaling (h : SchwartzMap ℝ ℝ) (hC : HasCompactSupport h) :
    let M := fun (ε : ℝ) (z : ℂ) ↦
      (∫ x : ℝ, Complex.exp ((ε : ℂ)*(z-1/2)*(x:ℂ)) * (h x : ℂ)).re
    let F := fun u : ℝ ↦
      (FourierTransform.fourier (fun x : ℝ ↦ (h x : ℂ)) u).re
    (∃ ε₀ > (0 : ℝ), ∃ C ≥ (0 : ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ →
      Summable (fun z : {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im} ↦
        (Zeta23.zeroMult z.val : ℝ) * M ε z.val) ∧
      |2*ε*(∑' z : {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im},
          (Zeta23.zeroMult z.val : ℝ) * M ε z.val) - h 0 * Real.log ε⁻¹| ≤ C) ∧
    Filter.Tendsto
      (fun ε : ℝ ↦ ∑' z : {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im},
        (2*ε)*((Zeta23.zeroMult z.val : ℝ) *
          (M ε z.val - F (ε*z.val.im/(2*Real.pi)))))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (0 : ℝ)) := by sorry
