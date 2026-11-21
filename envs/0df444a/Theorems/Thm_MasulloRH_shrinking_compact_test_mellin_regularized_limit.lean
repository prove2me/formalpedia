-- Prove2me | Theorems.Thm_MasulloRH_shrinking_compact_test_mellin_regularized_limit
-- name    : MasulloRH.shrinking_compact_test_mellin_regularized_limit
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:50:44.246571+00:00
-- url     : https://prove2.me/theorems/91d6a418-bd6a-4f77-b4f4-706a7bc88b35
-- title:
--   Finite term of the genuine shrinking-test Mellin zero sum
-- statement:
--   Let $h$ be a real smooth compactly supported function on $\mathbb R$. Define
--   $$
--   S_\varepsilon(h)=2\varepsilon\sum_{\gamma>0}m_\rho
--      \operatorname{Re}\int_{\mathbb R}h(x)e^{\varepsilon(\rho-1/2)x}\,dx,
--   $$
--   where distinct nontrivial zeta zeros $\rho=\beta+i\gamma$ of positive ordinate are indexed with their full analytic multiplicities $m_\rho$. With the additive Fourier phase $e^{-2\pi i ux}$, the finite term is
--   $$
--   \lim_{\varepsilon\downarrow0}\left(S_\varepsilon(h)-h(0)\log(1/\varepsilon)\right)
--   =\operatorname{Re}\int_{\mathbb R}\log|u|\,\widehat h(u)\,du.
--   $$
--   This is the additive Fourier pairing that enters the normalized real local finite part. Equivalently, the limit is $-\tfrac12 V(h)-(\gamma_{\!E}+\log(2\pi))h(0)$, with $V$ the finite part with counterterm $2h(0)\log\delta$ and $\gamma_{\!E}$ Euler's constant.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, 20 November 2026 draft, Chapter 13 and Appendix B, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf. Combines the weighted two-term Riemann–von Mangoldt formula (4d4dd796) and the strip Mellin comparison (aaa585f9). The equivalent real finite-part evaluation is 4ea36fe0.

import Mathlib
import Definitions.Def_Zeta23_Statement

open MeasureTheory

theorem MasulloRH.shrinking_compact_test_mellin_regularized_limit (h : SchwartzMap ℝ ℝ) (hC : HasCompactSupport h) :
    Filter.Tendsto
      (fun ε : ℝ ↦ 2*ε*(∑' z : {z : ℂ // Zeta23.IsNontrivialZero z ∧ 0 < z.im},
          (Zeta23.zeroMult z.val : ℝ) *
            (∫ x : ℝ, Complex.exp ((ε:ℂ)*(z.val-1/2)*(x:ℂ)) * (h x : ℂ)).re) -
        h 0*Real.log ε⁻¹)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((∫ u : ℝ, (Real.log |u| : ℂ) *
        FourierTransform.fourier (fun x : ℝ ↦ (h x : ℂ)) u).re)) := by sorry
