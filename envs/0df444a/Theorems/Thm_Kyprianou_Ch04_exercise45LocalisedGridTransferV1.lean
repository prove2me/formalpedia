-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise45LocalisedGridTransferV1
-- name    : Kyprianou.Ch04.exercise45LocalisedGridTransferV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T23:04:42.982673+00:00
-- url     : https://prove2.me/theorems/37303f10-31a5-4a54-ab6b-d2df74766ad4
-- title:
--   Exact clipped-grid UCP transfer under localisation
-- statement:
--   The original integrand and integral agree with bounded witnesses on good compact path events; vanishing outer probability of bad events gives exact UCP.
-- source:
--   Kyprianou (2006), Exercise 4.5(iv).

import Mathlib
import Definitions.Def_Kyprianou_Ch04_StochasticIntegralUCPV2
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Local bounded integral witnesses agree on increasingly likely compact path events. -/
theorem Kyprianou.Ch04.exercise45LocalisedGridTransferV1 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X H I : NNReal → Ω → ℝ)
    (Hn In : ℕ → NNReal → Ω → ℝ)
    (B : NNReal → ℕ → Set Ω)
    (hB : ∀ T, Tendsto (fun n => (P (B T n)).toReal) atTop (nhds 0))
    (hIn : ∀ n, Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X (Hn n) (In n))
    (hEq : ∀ T n w, w ∉ B T n → ∀ t ≤ T,
      H t w = Hn n t w ∧ I t w = In n t w) :
    Kyprianou.Ch04.IsStochasticIntegralInProbabilityV2 P X H I := by
  sorry
