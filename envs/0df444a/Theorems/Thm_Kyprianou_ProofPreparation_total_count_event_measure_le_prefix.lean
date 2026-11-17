-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_total_count_event_measure_le_prefix
-- name    : Kyprianou.ProofPreparation.total_count_event_measure_le_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:55.712202+00:00
-- url     : https://prove2.me/theorems/f909d779-d884-4368-a2cc-5f6f5d243a4d
-- title:
--   Kyprianou.ProofPreparation.total_count_event_measure_le_prefix
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.total_count_event_measure_le_prefix from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
-- source:
--   candidate-decomposition:2004a3aa-1f5c-4edd-8bf7-f67523bab94c:81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Complex
open scoped NNReal ENNReal Nat Topology
set_option autoImplicit false

namespace Kyprianou.ProofPreparation
theorem total_count_event_measure_le_prefix
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (N : ℕ → Ω → ℕ)
    (n m : ℕ) :
    P {ω | (∑' k, ((N k ω : ℕ) : ENNReal)) ≤ m} ≤
      P {ω | (∑ k ∈ Finset.range (n + 1), N k ω) ≤ m} := by sorry
end Kyprianou.ProofPreparation
