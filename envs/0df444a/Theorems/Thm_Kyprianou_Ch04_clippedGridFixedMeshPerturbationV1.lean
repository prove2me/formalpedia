-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedGridFixedMeshPerturbationV1
-- name    : Kyprianou.Ch04.clippedGridFixedMeshPerturbationV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:25:36.256648+00:00
-- url     : https://prove2.me/theorems/0279e75c-6d6c-4110-8093-cac2e4487b65
-- title:
--   clippedGridFixedMeshPerturbationV1
-- statement:
--   Use finite sum triangle inequality and the uniform state/weight perturbation bounds on the fixed clipped mesh.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- At a fixed finite mesh, uniform state and coefficient errors give a
deterministic uniform grid-sum perturbation bound. -/

theorem Kyprianou.Ch04.clippedGridFixedMeshPerturbationV1 (Y Z H L : NNReal → ℝ) (T : NNReal) (u : ℕ → NNReal) (n : ℕ)
    (K B d e : ℝ) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hd : 0 ≤ d) (he : 0 ≤ e)
    (hY : ∀ t ≤ T, |Y t - Z t| ≤ d)
    (hZ : ∀ t ≤ T, |Z t| ≤ B)
    (hH : ∀ k ∈ Finset.range n, |H (u k)| ≤ K)
    (hL : ∀ k ∈ Finset.range n, |H (u k) - L (u k)| ≤ e) :
    ∀ t ≤ T, |(∑ k ∈ Finset.range n, H (u k) *
      (Y (min t (u (k+1))) - Y (min t (u k)))) -
      (∑ k ∈ Finset.range n, L (u k) *
      (Z (min t (u (k+1))) - Z (min t (u k))))| ≤
        (n : ℝ) * (2*K*d + 2*B*e) := by
  sorry
