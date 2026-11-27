-- Prove2me | Theorems.Thm_MasulloRH_uniform_order_one_em_mesh_away_from_unit_height_zeros
-- name    : MasulloRH.uniform_order_one_em_mesh_away_from_unit_height_zeros
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T02:56:34.966349+00:00
-- url     : https://prove2.me/theorems/7bcd2f88-2ee3-525f-a657-edd5740c458b
-- title:
--   One common Euler–Maclaurin order and mesh resolution on compact zero-free sets
-- statement:
--   A point in a Masullo unit-height rectangle has an original rational-ball certificate exactly when zeta is nonzero there. On every compact zero-free subset, all sufficiently fine uniform meshes pass at every node whose ball meets the subset, using order one and truncation equal to the mesh resolution.
-- source:
--   For the existing Masullo unit-height Euler–Maclaurin ball obligation https://prove2.me/theorems/458479ec-80ed-41ca-9e08-9f4753b887b0 .

import Definitions.Def_MasulloRH_UnitHeightMeshes
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Set MasulloRH.UnitHeightMeshes

theorem MasulloRH.uniform_order_one_em_mesh_away_from_unit_height_zeros :
    (∀ n k : ℕ, ∀ s ∈ rect n k, covered n k s ↔ riemannZeta s ≠ 0) ∧
    (∀ n k : ℕ, ∀ S : Set ℂ, IsCompact S → S ⊆ rect n k → (∀ s ∈ S, riemannZeta s ≠ 0) →
      ∃ B : ℕ, ∀ m ≥ B, 0 < m ∧ ∀ i ≤ m, ∀ j ≤ m,
        (∃ s ∈ S, dist s (rationalCenter (node n k m i j)) < (rad m:ℝ)) → passes n k m i j) := by sorry
