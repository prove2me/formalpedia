-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_count_sum_ae_finite_of_summable_rates
-- name    : Kyprianou.ProofPreparation.poisson_count_sum_ae_finite_of_summable_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:35.411206+00:00
-- url     : https://prove2.me/theorems/ff04686a-d10c-4804-a771-ded19210c152
-- title:
--   Kyprianou.ProofPreparation.poisson_count_sum_ae_finite_of_summable_rates
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.poisson_count_sum_ae_finite_of_summable_rates from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem poisson_count_sum_ae_finite_of_summable_rates
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hfinite : (∑' k, (rate k : ENNReal)) < ⊤) :
    ∀ᵐ w ∂P, (∑' k, ((N k w : Nat) : ENNReal)) < ⊤ := by sorry
end Kyprianou.ProofPreparation
