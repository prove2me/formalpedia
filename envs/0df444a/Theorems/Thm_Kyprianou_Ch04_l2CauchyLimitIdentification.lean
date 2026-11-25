-- Prove2me | Theorems.Thm_Kyprianou_Ch04_l2CauchyLimitIdentification
-- name    : Kyprianou.Ch04.l2CauchyLimitIdentification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T21:25:26.3728+00:00
-- url     : https://prove2.me/theorems/6d98a04d-008c-5c9a-9f76-3cc3993c1f7d
-- title:
--   Identify the L2 limit of a Cauchy sequence using convergence in measure
-- statement:
--   A sequence of square-integrable functions Cauchy in L2 that converges in measure to a specified function converges in L2 to that function, which is itself square-integrable.
-- source:
--   Completeness of L2 and uniqueness of the limit in measure; used in Kyprianou Chapter 4 Exercise 4.4.

import Mathlib
open MeasureTheory Filter
open scoped ENNReal NNReal Topology
set_option autoImplicit false
universe u

theorem Kyprianou.Ch04.l2CauchyLimitIdentification
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℕ → Ω → ℝ) (Y : Ω → ℝ)
    (hX : ∀ n, MemLp (X n) 2 P)
    (hC : CauchySeq (fun n => (hX n).toLp (X n)))
    (hY : TendstoInMeasure P X atTop Y) :
    ∃ h : MemLp Y 2 P,
      Tendsto (fun n => (hX n).toLp (X n)) atTop (𝓝 (h.toLp Y)) := by
  sorry
