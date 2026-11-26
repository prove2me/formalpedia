-- Prove2me | Theorems.Thm_Kyprianou_Ch05_pointFamilyNonnegativeTimeKLSBridgeV1
-- name    : Kyprianou.Ch05.pointFamilyNonnegativeTimeKLSBridgeV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T15:46:49.767699+00:00
-- url     : https://prove2.me/theorems/788b4d7f-4b79-4bd0-849a-e978aa5bdfa0
-- title:
--   Restrict a canonical point family to a Chapter 4 Poisson random measure
-- statement:
--   Use the proved Chapter 2 finite and infinite evaluation laws and countable disjoint independence; derive the past/future sigma-algebra field from independent region sigma algebras.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch05.pointFamilyNonnegativeTimeKLSBridgeV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Ω → ℕ) (Z : ℕ → ℕ → Ω → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) P) :
    ∃ N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0,0,0} P Pi,
      ∀ w, N.N w = (poissonRandomMeasure K Z w).restrict (Ici (0 : ℝ) ×ˢ univ) := by
  sorry
