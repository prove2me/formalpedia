-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_bounded_event_probability
-- name    : Kyprianou.ProofPreparation.poisson_prefix_bounded_event_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:53.125265+00:00
-- url     : https://prove2.me/theorems/fc8148cd-908c-41d9-8652-79d5cdd6b1ec
-- title:
--   Kyprianou.ProofPreparation.poisson_prefix_bounded_event_probability
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.poisson_prefix_bounded_event_probability from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem poisson_prefix_bounded_event_probability
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (rate : ℕ → ℝ≥0) (N : ℕ → Ω → ℕ)
    (hN : ∀ k, AEMeasurable (N k) P)
    (hpref : ∀ n,
      P.map (fun ω => ∑ k ∈ Finset.range (n + 1), N k ω) =
        poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k))
    (n m : ℕ) :
    P {ω | (∑ k ∈ Finset.range (n + 1), N k ω) ≤ m} =
      (poissonMeasure (∑ k ∈ Finset.range (n + 1), rate k))
        (Set.Iic m) := by sorry
end Kyprianou.ProofPreparation
