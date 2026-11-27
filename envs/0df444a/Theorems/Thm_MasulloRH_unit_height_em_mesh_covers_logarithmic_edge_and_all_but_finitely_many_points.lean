-- Prove2me | Theorems.Thm_MasulloRH_unit_height_em_mesh_covers_logarithmic_edge_and_all_but_finitely_many_points
-- name    : MasulloRH.unit_height_em_mesh_covers_logarithmic_edge_and_all_but_finitely_many_points
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-27T02:56:33.096697+00:00
-- url     : https://prove2.me/theorems/ba814e21-2a8a-55b2-b52d-a8b14f62b398
-- title:
--   Logarithmically many possible exceptions and a certified horizontal interval in every high band
-- statement:
--   At integer height T≥100000 the only possible uncertified points form one set of at most A log(T+3) actual zeros for the whole band. A logarithmic strip at the right edge passes uniformly. Every band contains a rational horizontal interval of length at least 1/[4(A log(T+3)+1)] covered across all its target rectangles. Full coverage is equivalent to the finite interior mesh tests.
-- source:
--   For the existing Masullo unit-height Euler–Maclaurin ball obligation https://prove2.me/theorems/458479ec-80ed-41ca-9e08-9f4753b887b0 . Classical analytic inputs are the local multiplicity-weighted count https://prove2.me/submissions/d63d69d7-6b8e-42e4-9222-57b07829adb8 and Davenport’s logarithmic zero-free region https://prove2.me/submissions/dc0549e1-d469-4a08-a0a3-ec60c0d1b76e .

import Definitions.Def_MasulloRH_UnitHeightMeshes
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Set MasulloRH.UnitHeightMeshes

theorem MasulloRH.unit_height_em_mesh_covers_logarithmic_edge_and_all_but_finitely_many_points :
    (∃ c A : ℝ, 0 < c ∧ 1 ≤ A ∧
      (∀ n k : ℕ, ∃ B : ℕ, ∀ m ≥ B, 0 < m ∧ ∀ i ≤ m, ∀ j ≤ m,
        (∃ s ∈ rect n k, cutoff n c ≤ s.re ∧
          dist s (rationalCenter (node n k m i j)) < (rad m:ℝ)) → passes n k m i j) ∧
      (∀ n : ℕ, ∃ E : Finset ℂ,
        (E.card:ℝ) ≤ A*Real.log ((100000:ℝ)+n+3) ∧
        (∀ z ∈ E, 1/2 < z.re ∧ z.re < cutoff n c ∧ riemannZeta z = 0) ∧
        (∀ k : ℕ, ∀ s ∈ rect n k, covered n k s ↔ s ∉ E) ∧
        ∃ a b : ℚ, (100000:ℝ)+n+1/2 ≤ (a:ℝ) ∧ (b:ℝ) ≤ (100000:ℝ)+n+1 ∧
          1/(4*(A*Real.log ((100000:ℝ)+n+3)+1)) ≤ (b:ℝ)-(a:ℝ) ∧
          ∀ k : ℕ, ∀ s ∈ rect n k, s.im ∈ Icc (a:ℝ) (b:ℝ) → covered n k s)) ∧
    (innerMeshes ↔ ∀ n k : ℕ, ∀ s ∈ rect n k, covered n k s) := by sorry
