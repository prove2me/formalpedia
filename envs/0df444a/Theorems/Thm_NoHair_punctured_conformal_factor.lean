-- Prove2me | Theorems.Thm_NoHair_punctured_conformal_factor
-- name    : NoHair.punctured_conformal_factor
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:21:24.163813+00:00
-- url     : https://prove2.me/theorems/629265e5-c315-4a1c-911d-8a19a8665ab3
-- title:
--   Rigidity of the harmonic conformal factor on punctured three-space
-- statement:
--   Let $U$ be harmonic on Euclidean three-space with its origin removed. Suppose $U(x)\to1$ uniformly as $|x|\to\infty$ and $|x|\,U(x)\to b$ as $x\to0$. Then
--   $$U(x)=1+\frac b{|x|}\qquad (x\ne0).$$
--   The assumptions allow angular dependence in both limits. This is the scalar uniqueness step after the zero-mass conformal double of a static vacuum slice has been identified with Euclidean space. It determines the complete conformal factor and its horizon level set from the two ends.
-- source:
--   Spherical barrier argument for the harmonic conformal factor in the static vacuum conformal-doubling construction. G. L. Bunting and A. K. M. Masood-ul-Alam, Nonexistence of Multiple Black Holes in Asymptotically Euclidean Static Vacuum Space-Time, Gen. Relativ. Gravit. 19, 147–154 (1987), https://doi.org/10.1007/BF00770326. The strong maximum principle is Hunter, Notes on Partial Differential Equations, Theorem 2.13.

import Mathlib

open Set InnerProductSpace

theorem NoHair.punctured_conformal_factor (U : EuclideanSpace ℝ (Fin 3) → ℝ) (b : ℝ)
    (hU : HarmonicOnNhd U ({0}ᶜ))
    (hfar : ∀ ε : ℝ, 0 < ε → ∃ L : ℝ, ∀ x, L < ‖x‖ → |U x - 1| ≤ ε)
    (h₀ : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ x, 0 < ‖x‖ → ‖x‖ < δ → |‖x‖ * U x - b| ≤ ε) :
    ∀ x, x ≠ 0 → U x = 1 + b / ‖x‖ := by sorry
