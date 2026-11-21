-- Prove2me | Theorems.Thm_MasulloRH_quadratic_mertens_prefix_bounds
-- name    : MasulloRH.quadratic_mertens_prefix_bounds
-- status  : Open
-- author  : @marozols
-- created : 2026-11-21T04:03:21.169695+00:00
-- url     : https://prove2.me/theorems/d54aa28d-53c5-4ce6-a2b6-28f51f345da9
-- title:
--   Subpower excess over quadratic growth for finite unweighted Mertens energies
-- statement:
--   For every positive d, some C≥0 bounds Σ_{k=1}^N M(k)² by C(N+1)^(2+d) at every N. The ordinary sharp Möbius prefix sums may fluctuate within this quadratic mean. The exponent has arbitrarily small positive slack.
-- source:
--   Single open finite-arithmetic mean-square input for the ordinary Mertens frontier 7abb4d24. The proved inverse-zeta Mellin criterion identifies it with ordinary RH and distinguishes the necessarily divergent endpoint Dirichlet series.

import Mathlib
set_option autoImplicit false

open Finset ArithmeticFunction
namespace MasulloRH

theorem quadratic_mertens_prefix_bounds :
    let M (n : ℕ) : ℝ := ∑ i ∈ Finset.Icc 1 n,(moebius i:ℝ)
    ∀ d : ℝ,0<d → ∃ C : ℝ,0≤C ∧ ∀ N : ℕ,
      (∑ n ∈ range N,(M (n+1))^2) ≤ C*((N:ℝ)+1)^(2+d) := by sorry

end MasulloRH
