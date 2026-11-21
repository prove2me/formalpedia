-- Prove2me | Theorems.Thm_GRH_liouville_harmonic_le_of_moebius_harmonic_le
-- name    : GRH.liouville_harmonic_le_of_moebius_harmonic_le
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:35:37.915711+00:00
-- url     : https://prove2.me/theorems/ca0f885d-0502-476c-a262-63b801881ece
-- title:
--   Square-divisor transfer of harmonic Möbius decay to harmonic Liouville decay
-- statement:
--   For $1/2<\sigma\le1$, a bound $|\sum_{j\le X}\mu(j)/j|\le C(X+1)^{\sigma-1}$ for every cutoff implies $$\left|\sum_{j\le U}\lambda(j)/j\right|\le C\zeta(2\sigma)(U+1)^{\sigma-1}.$$ The finite square-divisor convolution gives the multiplier at the same exponent and introduces no cutoff loss.
-- source:
--   The classical square-divisor convolution for the Möbius and Liouville functions, in the harmonic normalization needed for GRH.reduced_liouville_harmonic_power_decay (005c4a44).

import Definitions.Def_GRH_SquarefreeBilinear

set_option autoImplicit false

open Finset ArithmeticFunction
open scoped BigOperators
namespace GRH

theorem liouville_harmonic_le_of_moebius_harmonic_le (σ C : ℝ) (hhalf : 1/2 < σ) (hone : σ ≤ 1) (hC : 0 ≤ C)
    (H : ∀ U : ℕ, |∑ j ∈ range (U+1), (moebius j : ℝ) / j| ≤ C * ((U:ℝ)+1)^(σ-1))
    (U : ℕ) :
    |reducedLiouvilleHarmonic 1 U| ≤
      (C * ∑' d : ℕ, ((d:ℝ)^(2*σ))⁻¹) * ((U:ℝ)+1)^(σ-1) := by sorry

end GRH
