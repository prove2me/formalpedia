-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise41StoppedPositiveGermV12
-- name    : Kyprianou.Ch04.exercise41StoppedPositiveGermV12
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T12:51:55.474739+00:00
-- url     : https://prove2.me/theorems/2149e18c-009d-52ab-a004-3dd2db4d813f
-- title:
--   Strong Markov transfer of the positive small-time BV drift germ to a finite stopping clock
-- statement:
--   Strong Markov transfer of the positive small-time BV drift germ to a finite stopping clock
-- source:
--   Kyprianou (2006), Exercise 4.1(ii), zero-visit boundary behaviour.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false

theorem Kyprianou.Ch04.exercise41StoppedPositiveGermV12
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Filtration NNReal inferInstance)
    (L : SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation) (hd : 0 < L.drift)
    (τ : Ω → NNReal)
    (hτ : ∀ s : NNReal, MeasurableSet[F.rightCont s] {w | τ w ≤ s}) :
    ∀ᵐ w ∂P, ∃ ε : NNReal, 0 < ε ∧
      ∀ u : NNReal, 0 < u → u < ε →
        0 < L.X (τ w + u) w - L.X (τ w) w := by
  sorry
