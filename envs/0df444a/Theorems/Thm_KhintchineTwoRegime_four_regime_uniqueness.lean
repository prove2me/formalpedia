-- Prove2me | Theorems.Thm_KhintchineTwoRegime_four_regime_uniqueness
-- name    : KhintchineTwoRegime.four_regime_uniqueness
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:36:23.029878+00:00
-- url     : https://prove2.me/theorems/2c516989-70ec-40ad-9cab-71c90c6b9803
-- title:
--   Uniqueness of the four-coordinate equality profile
-- statement:
--   Let $n\ge4$ and $0\le\tau\le\sqrt{2-\sqrt2}$. If $\omega\in\mathcal C_n(\tau)$ satisfies
--
--   $$
--   K_n(\omega)=\frac1{\sqrt2}+
--   \Bigl(\sqrt{1-\frac{\tau^2}{4}}-\tau\Bigr)\frac{\tau}{2\sqrt2},
--   $$
--
--   then $\omega=\omega_\tau=(r,r,s,s,0,\ldots,0)$, the four-coordinate profile of Theorem 1.
--
--   Hence equality in the four-coordinate Khintchine bound has a unique representative in the proper chamber. At $\tau=0$ this representative is $\omega^*$; for $\tau>0$ equality forces the first two coordinates to agree and forces the normalized tail to be a two-coordinate Szarek extremizer.
--
--   **Formalization Note** Uniqueness is equality of vectors `Fin n → ℝ`, not merely equality up to permutations or sign changes.
-- source:
--   Fang–Wang, A Two-regime Khintchine Inequality and an Improved Bound on the Degree-1 Fourier Weight for Linear Threshold Functions, arXiv:2608.27908v2, Theorem 1, p.4, and the equality analysis in its proof, p.5.

import Mathlib
import Definitions.Def_KhintchineTwoRegime_K
import Definitions.Def_KhintchineTwoRegime_Cn
import Definitions.Def_KhintchineTwoRegime_fourProfile

theorem KhintchineTwoRegime.four_regime_uniqueness (n : ℕ) (hn : 4 ≤ n) (τ : ℝ)
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ Real.sqrt (2 - Real.sqrt 2))
    (ω : Fin n → ℝ) (hω : ω ∈ Cn n τ)
    (hK : K n ω = 1 / Real.sqrt 2 +
      (Real.sqrt (1 - τ ^ 2 / 4) - τ) * (τ / (2 * Real.sqrt 2))) :
    ω = fourProfile n τ := by sorry
