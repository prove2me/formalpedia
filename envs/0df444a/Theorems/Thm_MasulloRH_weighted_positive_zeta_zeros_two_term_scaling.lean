-- Prove2me | Theorems.Thm_MasulloRH_weighted_positive_zeta_zeros_two_term_scaling
-- name    : MasulloRH.weighted_positive_zeta_zeros_two_term_scaling
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:40:56.500365+00:00
-- url     : https://prove2.me/theorems/4d4dd796-56b4-43a8-8769-8788ac706f86
-- title:
--   Two-term Riemann–von Mangoldt scaling for positive-zero Schwartz weights
-- statement:
--   Let $F$ be a real Schwartz function and let $\rho=\beta+i\gamma$ range over the distinct nontrivial zeros of the Riemann zeta function of positive ordinate, with analytic multiplicity $m_\rho$. As $0<\varepsilon\le1$ varies, the weighted sum is absolutely convergent and
--   $$
--   \begin{aligned}
--   \varepsilon\sum_{\gamma>0}m_\rho F(\varepsilon\gamma)
--   ={}&\frac{\log(1/\varepsilon)}{2\pi}\int_0^\infty F(u)\,du\\
--   &+\frac1{2\pi}\int_0^\infty \bigl(\log u-\log(2\pi)\bigr)F(u)\,du
--   +O_F\!\left(\varepsilon(1+\log(1/\varepsilon))\right).
--   \end{aligned}
--   $$
--   The two-term expansion keeps the finite part of the Riemann–von Mangoldt main term. It applies to all positive nontrivial zero locations, with the real part of each zero retained in the index so that equal ordinates at distinct locations are counted separately.
-- source:
--   Riemann–von Mangoldt formula in the cumulative convention (0,T], https://prove2.me/theorems/a365b15d-8cc3-467c-bb49-2d3705c8b1b2. Strengthens positive-zero Schwartz scaling b09a7d33-47b1-4164-9eba-bc59bdc01b20 for the shrinking tests in Alessandro Maria Masullo, The Music of the Primes, Chapter 13 (20 November 2026 draft), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf.

import Mathlib
import Definitions.Def_Zeta23_Statement

open MeasureTheory

theorem MasulloRH.weighted_positive_zeta_zeros_two_term_scaling (F : SchwartzMap ℝ ℝ) :
    ∃ C ≥ (0:ℝ), ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Summable (fun ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im} ↦
        (Zeta23.zeroMult ρ.val : ℝ)*F (ε*ρ.val.im)) ∧
      |ε*(∑' ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im},
          (Zeta23.zeroMult ρ.val : ℝ)*F (ε*ρ.val.im)) -
          (1/(2*Real.pi))*Real.log ε⁻¹*(∫ u in Set.Ioi (0:ℝ), F u) -
          (1/(2*Real.pi))*(∫ u in Set.Ioi (0:ℝ), (Real.log u-Real.log (2*Real.pi))*F u)| ≤
        C*ε*(1+Real.log ε⁻¹) := by sorry
