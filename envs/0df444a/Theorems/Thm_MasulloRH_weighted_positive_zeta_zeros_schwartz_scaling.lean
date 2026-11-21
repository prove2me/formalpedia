-- Prove2me | Theorems.Thm_MasulloRH_weighted_positive_zeta_zeros_schwartz_scaling
-- name    : MasulloRH.weighted_positive_zeta_zeros_schwartz_scaling
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:07:29.404242+00:00
-- url     : https://prove2.me/theorems/b09a7d33-47b1-4164-9eba-bc59bdc01b20
-- title:
--   Schwartz-weighted asymptotic for positive zeta ordinates
-- statement:
--   Let $F$ be any real Schwartz function on the real line. Write $\rho=\beta+i\gamma$ for a distinct zero of $\zeta$ with $0<\beta<1$ and $\gamma>0$, and let $m_\rho$ be its multiplicity. For $0<\varepsilon\le 1$ the series $\sum_\rho m_\rho F(\varepsilon\gamma)$ is summable, and
--   $$\varepsilon\sum_\rho m_\rho F(\varepsilon\gamma)
--   =\frac{\log(1/\varepsilon)}{2\pi}\int_0^\infty F(u)\,du+O_F(1).$$
--   The error is uniform over all such $\varepsilon$. The weights need no sign condition. This is the positive-height counting estimate used to analyze shrinking tests in the rational case of Masullo’s equation (13.3.1.3).
-- source:
--   Weighted consequence of Titchmarsh–Heath-Brown, The Theory of the Riemann Zeta-function, 2nd ed., Theorem 9.4, §9.3–9.4, https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf. Application to Masullo, The Music of the Primes, 20 November 2026 draft, p. 522, Eq. (13.3.1.3), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf.

import Mathlib
import Definitions.Def_Zeta23_Statement

open MeasureTheory
open scoped SchwartzMap

theorem MasulloRH.weighted_positive_zeta_zeros_schwartz_scaling (F : 𝓢(ℝ, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      Summable (fun ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im} ↦
        (Zeta23.zeroMult ρ.val : ℝ) * F (ε * ρ.val.im)) ∧
      |ε * (∑' ρ : {ρ : ℂ // Zeta23.IsNontrivialZero ρ ∧ 0 < ρ.im},
            (Zeta23.zeroMult ρ.val : ℝ) * F (ε * ρ.val.im)) -
        (1 / (2 * Real.pi)) * Real.log ε⁻¹ * (∫ u in Set.Ioi (0 : ℝ), F u)| ≤ C := by sorry
