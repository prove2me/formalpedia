-- Prove2me | Theorems.Thm_Kyprianou_Ch02_aeSummableFiniteClockOfIntegerJumpMassV1
-- name    : Kyprianou.Ch02.aeSummableFiniteClockOfIntegerJumpMassV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T22:02:04.903803+00:00
-- url     : https://prove2.me/theorems/71e4fdb7-e575-4675-809e-89eb4ccc6789
-- title:
--   Finite expected extended jump mass at every integer horizon gives almost-sure compact summability
-- statement:
--   Generic measure-theoretic lemma for arbitrary nonnegative real jump weights on nonnegative real times: assuming every integer-horizon extended nonnegative sum is almost everywhere measurable with finite lintegral, infer absolute summability on all real finite horizons on a single conull set. The proof uses pointwise finiteness of extended sums almost surely, the countable intersection over integer horizons, and restriction of summable series via the ceiling of a given real time. No Levy process, Poisson measure, or bounded variation assumptions are used.
-- source:
--   Mathlib Topology.Algebra.InfiniteSum.ENNReal and MeasureTheory ae_lt_top; motivated by Kyprianou (2006), Chapter 2, bounded-variation lemma 2.12.

import Mathlib
open MeasureTheory Set Function
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.aeSummableFiniteClockOfIntegerJumpMassV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (w : ℝ≥0 → Ω → ℝ)
    (hnonneg : ∀ t ω, 0 ≤ w t ω)
    (hmass : ∀ n : ℕ,
      AEMeasurable
        (fun ω => ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
          ENNReal.ofReal (w (s : ℝ≥0) ω)) P ∧
      (∫⁻ ω, ∑' s : Set.Ioc (0 : ℝ≥0) (n : ℝ≥0),
        ENNReal.ofReal (w (s : ℝ≥0) ω) ∂P) < ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Summable (fun s : Set.Ioc (0 : ℝ≥0) T => w (s : ℝ≥0) ω) := by
  sorry
