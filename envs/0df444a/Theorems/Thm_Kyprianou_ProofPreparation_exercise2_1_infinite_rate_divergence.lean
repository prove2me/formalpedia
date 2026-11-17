-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_exercise2_1_infinite_rate_divergence
-- name    : Kyprianou.ProofPreparation.exercise2_1_infinite_rate_divergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:48.296614+00:00
-- url     : https://prove2.me/theorems/e71d6da9-deb1-468d-8028-19f47e7af498
-- title:
--   Kyprianou.ProofPreparation.exercise2_1_infinite_rate_divergence
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.exercise2_1_infinite_rate_divergence from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem exercise2_1_infinite_rate_divergence
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P)
    (hdiv : (∑' k, (rate k : ENNReal)) = ⊤) :
    ∀ᵐ w ∂P, (∑' k, ((N k w : Nat) : ENNReal)) = ⊤ := by sorry
end Kyprianou.ProofPreparation
