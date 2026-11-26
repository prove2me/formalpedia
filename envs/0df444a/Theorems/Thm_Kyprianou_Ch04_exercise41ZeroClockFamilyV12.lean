-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41ZeroClockFamilyV12
-- name    : Kyprianou.Ch04.exercise41ZeroClockFamilyV12
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:51:50.096789+00:00
-- url     : https://prove2.me/theorems/72e55a2d-933b-4f38-816e-063ab5532c42
-- title:
--   A countable family of finite right-continuous stopping clocks covers all actual zero visits almost surely
-- statement:
--   A countable family of finite right-continuous stopping clocks covers all actual zero visits almost surely
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), zero-visit boundary behaviour.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41ZeroClockFamilyV12
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift) :
    ∃ τ : ℕ → ℕ → Ω → NNReal,
      (∀ j N s, MeasurableSet[F.rightCont s] {w | τ j N w ≤ s}) ∧
      (∀ᵐ w ∂P, ∀ s : NNReal, L.X s w = 0 →
        ∃ j N, τ j N w = s) := by
  sorry
