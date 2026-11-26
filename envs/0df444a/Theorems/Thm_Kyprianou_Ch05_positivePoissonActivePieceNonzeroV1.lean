-- Prove2me | Theorems.Thm_Kyprianou_Ch05_positivePoissonActivePieceNonzeroV1
-- name    : Kyprianou.Ch05.positivePoissonActivePieceNonzeroV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:54:31.462824+00:00
-- url     : https://prove2.me/theorems/9a21248a-3ec5-483f-944b-81eb0588b228
-- title:
--   Every active Poisson index belongs to a positive intensity piece
-- statement:
--   A zero-intensity piece has a Poisson count with rate zero and hence count zero almost surely. Take the intersection of the countably many conull implications.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.positivePoissonActivePieceNonzeroV1
    {Lambda : Type} [MeasurableSpace Lambda]
    (Q : Measure Lambda) [IsProbabilityMeasure Q]
    (Pi : Measure ℝ) [SigmaFinite Pi]
    (K : ℕ → Lambda → ℕ) (Z : ℕ → ℕ → Lambda → ℝ × ℝ)
    (hd : IsPoissonPointFamily K Z ((volume : Measure ℝ).prod Pi) Q) :
    ∀ᵐ w ∂Q, ∀ k n : ℕ, n < K k w →
      ((volume : Measure ℝ).prod Pi) (prmPiece ((volume : Measure ℝ).prod Pi) k) ≠ 0 := by
  sorry
