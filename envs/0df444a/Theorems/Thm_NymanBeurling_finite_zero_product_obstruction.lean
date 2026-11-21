-- Prove2me | Theorems.Thm_NymanBeurling_finite_zero_product_obstruction
-- name    : NymanBeurling.finite_zero_product_obstruction
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T01:22:51.079999+00:00
-- url     : https://prove2.me/theorems/af94a689-5b66-4568-a5d3-7d09bc8cc587
-- title:
--   A finite Burnol product lower bound for rational remainder certificates
-- statement:
--   Let S be any finite set of distinct zeros ρ of the Riemann zeta function with Re(ρ)>1/2 and ρ≠1. For any finitely supported rational coefficient vector c and cutoff H, the rational certificate C_H(c) used in the Bagchi remainder criterion satisfies
--   1 − ∏_{ρ∈S}|1−1/ρ|² ≤ C_H(c).
--   Every distinct zero contributes a factor. The statement includes the empty set and does not require an assumption on zero multiplicities.
-- source:
--   J.-F. Burnol, A note on Nyman’s equivalent formulation of the Riemann hypothesis, https://arxiv.org/abs/math/9910055 . This specializes the finite distinct-zero product bound to the discrete certificate of the mission. See also B. Bagchi, https://arxiv.org/abs/math/0607733 .

import Mathlib

theorem NymanBeurling.finite_zero_product_obstruction (S : Finset {z : ℂ // (1/2:ℝ)<z.re})
    (hS : ∀ z ∈ S, z.val≠1 ∧ riemannZeta z.val=0) (c : ℕ →₀ ℚ) (H : ℕ) :
    1 - ∏ z ∈ S, ‖1-1/z.val‖^2 ≤
      (((∑ n ∈ Finset.range H, (1 - ∑ k ∈ c.support, c k *
          (((n+1) % (k+2) : ℕ) : ℚ) / ((k+2 : ℕ) : ℚ))^2 /
          ((n+1 : ℚ)*(n+2 : ℚ))) +
      (1 + ∑ k ∈ c.support, |c k|)^2/(H+1) : ℚ) : ℝ) := by sorry
