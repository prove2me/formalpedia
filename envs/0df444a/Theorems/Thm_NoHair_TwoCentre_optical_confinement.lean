-- Prove2me | Theorems.Thm_NoHair_TwoCentre_optical_confinement
-- name    : NoHair.TwoCentre.optical_confinement
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T21:31:54.560092+00:00
-- url     : https://prove2.me/theorems/d9d2c704-d533-4159-bc3a-a02c840449e7
-- title:
--   Finite travel time confines two-centre causal curves away from both poles
-- statement:
--   Fix two poles $b_1,b_2$ in Euclidean three-space, a regular initial position $x_0$, and a nonnegative budget $L$ for elapsed coordinate time. For the two-centre static electrovacuum, $U(x)=1+|x-b_1|^{-1}+|x-b_2|^{-1}$. There exists a compact spatial set $K$ excluding both poles such that every differentiable curve from $x_0$ satisfying the future causal bound $U(x)^2|x'|\leq t'$ remains in $K$ as long as $t(s)-t(0)\leq L$. The same $K$ works for all such curves.
-- source:
--   J. B. Hartle and S. W. Hawking, Solutions of the Einstein-Maxwell equations with many black holes, Commun. Math. Phys. 26 (1972), 87–101, §II, equations (2.1)–(2.13), https://doi.org/10.1007/BF01645696. Optical metric of the static line element in equation (2.1).

import Mathlib

open Set

theorem NoHair.TwoCentre.optical_confinement
    (b₁ b₂ x₀ : EuclideanSpace ℝ (Fin 3)) (h₁ : x₀ ≠ b₁) (h₂ : x₀ ≠ b₂)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ K : Set (EuclideanSpace ℝ (Fin 3)), IsCompact K ∧ b₁ ∉ K ∧ b₂ ∉ K ∧
    ∀ (x dx : ℝ → EuclideanSpace ℝ (Fin 3)) (τ dτ : ℝ → ℝ),
      x 0 = x₀ →
      (∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt x (dx t) t ∧ HasDerivAt τ (dτ t) t ∧
        x t ≠ b₁ ∧ x t ≠ b₂ ∧
        (1 + 1 / ‖x t - b₁‖ + 1 / ‖x t - b₂‖) ^ 2 * ‖dx t‖ ≤ dτ t) →
      ∀ s ∈ Icc (0 : ℝ) 1, τ s - τ 0 ≤ L → x s ∈ K := by
  sorry
