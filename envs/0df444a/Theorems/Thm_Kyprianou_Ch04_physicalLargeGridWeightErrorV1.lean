-- Prove2me | Theorems.Thm_Kyprianou_Ch04_physicalLargeGridWeightErrorV1
-- name    : Kyprianou.Ch04.physicalLargeGridWeightErrorV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:36:33.416473+00:00
-- url     : https://prove2.me/theorems/096c2845-c042-40d1-8429-c9a423778a93
-- title:
--   physicalLargeGridWeightErrorV1
-- statement:
--   Finite-variation physical grid error bounded by the actual absolute marked ledger.
-- source:
--   Kyprianou (2006), Exercise 4.5(iii)

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The physical large-mark ledger gives a uniform finite-variation grid bound. -/

theorem Kyprianou.Ch04.physicalLargeGridWeightErrorV1 (R : Measure (ℝ × ℝ)) (T : NNReal)
    (S : Finset NNReal) (j Y H L : NNReal → ℝ) (b d : ℝ) (hd : 0 ≤ d)
    (u : ℕ → NNReal) (hu : Monotone u) (n : ℕ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ 1/2 < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1/2 < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (hY : ∀ t ≤ T, Y t = b * (t : ℝ) +
      ∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 ∂ R)
    (hH : ∀ k ∈ Finset.range n, |H (u k)-L (u k)| ≤ d) :
    ∀ t ≤ T, |(∑ k ∈ Finset.range n,H (u k) *
      (Y (min t (u (k+1)))-Y (min t (u k)))) -
      (∑ k ∈ Finset.range n,L (u k) *
      (Y (min t (u (k+1)))-Y (min t (u k))))| ≤
      (|b| * (T : ℝ)+(∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ
        {x : ℝ | 1/2 < |x|}, |z.2| ∂ R)) * d := by
  sorry
