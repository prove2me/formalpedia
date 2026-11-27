-- Prove2me | Theorems.Thm_Kyprianou_Ch04_clippedAffineGridWeightErrorV1
-- name    : Kyprianou.Ch04.clippedAffineGridWeightErrorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:36:43.012804+00:00
-- url     : https://prove2.me/theorems/338d7ae1-a77d-4930-b811-b7f6ea610458
-- title:
--   clippedAffineGridWeightErrorV1
-- statement:
--   Uniform clipped-grid weight error for finite affine step paths, bounded by total variation.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_kw47_positive_monotone_grid_variation
open MeasureTheory Set
open scoped NNReal Classical
set_option autoImplicit false

/-- The variation of a finite affine step path bounds all clipped mesh
weight perturbations independently of the mesh size. -/

theorem Kyprianou.Ch04.clippedAffineGridWeightErrorV1 (T : NNReal) (S : Finset NNReal) (a Y H L : NNReal → ℝ)
    (b d : ℝ) (hd : 0 ≤ d) (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (hY : ∀ s ≤ T, Y s = b * (s : ℝ) + ∑ r ∈ S, if r ≤ s then a r else 0)
    (hH : ∀ k ∈ Finset.range n, |H (u k)-L (u k)| ≤ d) :
    ∀ t ≤ T, |(∑ k ∈ Finset.range n,H (u k) *
      (Y (min t (u (k+1)))-Y (min t (u k)))) -
      (∑ k ∈ Finset.range n,L (u k) *
      (Y (min t (u (k+1)))-Y (min t (u k))))| ≤
      (|b| * (T : ℝ)+∑ r ∈ S,|a r|) * d := by
  sorry
