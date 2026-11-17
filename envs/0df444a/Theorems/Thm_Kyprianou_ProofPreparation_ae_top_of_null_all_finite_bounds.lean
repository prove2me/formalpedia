-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_ae_top_of_null_all_finite_bounds
-- name    : Kyprianou.ProofPreparation.ae_top_of_null_all_finite_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:43.793481+00:00
-- url     : https://prove2.me/theorems/d076aa5b-e499-466a-9164-1d83289390a2
-- title:
--   Kyprianou.ProofPreparation.ae_top_of_null_all_finite_bounds
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.ae_top_of_null_all_finite_bounds from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem ae_top_of_null_all_finite_bounds
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ENNReal)
    (hnull : ∀ m : ℕ, P {ω | f ω ≤ (m : ENNReal)} = 0) :
    ∀ᵐ ω ∂P, f ω = ⊤ := by sorry
end Kyprianou.ProofPreparation
