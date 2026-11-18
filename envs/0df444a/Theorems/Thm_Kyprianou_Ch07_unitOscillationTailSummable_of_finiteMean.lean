-- Prove2me | Theorems.Thm_Kyprianou_Ch07_unitOscillationTailSummable_of_finiteMean
-- name    : Kyprianou.Ch07.unitOscillationTailSummable_of_finiteMean
-- status  : Open
-- author  : @WillR
-- created : 2026-11-17T08:06:48.590853+00:00
-- url     : https://prove2.me/theorems/bc29c26b-ba82-4357-b964-dd60ff3f2170
-- title:
--   Finite-mean Lévy unit-block oscillations have summable linear-scale tails
-- statement:
--   For a real Lévy process whose unit-time increment has a finite first absolute moment, the probabilities of unit-block maxima exceeding n/(k+1) are summable over n for each natural k. The proof requires integrability and stationary-in-law unit-block maxima and an integrated-tail summability argument. Isolated as the hard substantive remaining child for Exercise 7.2(ii).
-- source:
--   Kyprianou (2006) Exercise 7.2(ii), printed p.207, first edition. Companion to the verified Borel-Cantelli step Kyprianou.Ch07.unitOscillationSublinear_of_summableTails; preserves all hypotheses from the original Exercise 7.2 statement.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RealLevyLawAndRegularityIntegrals
import Definitions.Def_Kyprianou_Ch07_UnitTimeOscillationObservables
import Definitions.Def_Kyprianou_Ch07_LevyMeanAndTailTests
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch07.unitOscillationTailSummable_of_finiteMean
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Omega → ℝ)
    (hX : Kyprianou.Ch06.IsRealLevyProcess P X)
    (hMoment : Integrable (fun omega => |X 1 omega|) P) :
    ∀ k : ℕ, (∑' n : ℕ,
      P {omega : Omega | ((k : ℝ) + 1)⁻¹ * (n : ℝ) ≤
        |Kyprianou.Ch07.maximalUnitIncrement X n omega|}) ≠ ⊤ := by sorry
