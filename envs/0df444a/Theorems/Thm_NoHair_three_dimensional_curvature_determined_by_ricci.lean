-- Prove2me | Theorems.Thm_NoHair_three_dimensional_curvature_determined_by_ricci
-- name    : NoHair.three_dimensional_curvature_determined_by_ricci
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T11:39:14.570802+00:00
-- url     : https://prove2.me/theorems/acbeaa36-ae60-4f3c-a672-cc2a67e19389
-- title:
--   Ricci contraction determines a doubly alternating curvature tensor in dimension three
-- statement:
--   In three dimensions each pair of skew indices is represented by one complementary index. For a symmetric invertible inverse metric, the Ricci contraction on these nine coefficients is injective. The result holds in arbitrary coordinates and requires only the two skew symmetries.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Mathlib

open Matrix

theorem NoHair.three_dimensional_curvature_determined_by_ricci (B : Matrix (Fin 3) (Fin 3) ℝ) (symm : B.IsSymm) (nonsing : B.det ≠ 0)
    (R : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (first : ∀ a b i j, R a b i j = -R b a i j)
    (last : ∀ a b i j, R a b i j = -R a b j i)
    (ric : ∀ b j, (∑ a : Fin 3, ∑ i : Fin 3, B a i * R a b i j) = 0) :
    ∀ a b i j, R a b i j = 0 := by sorry
