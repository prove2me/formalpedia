-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_finite_poisson_count_real_total_hasLaw
-- name    : Kyprianou.ProofPreparation.finite_poisson_count_real_total_hasLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:43.759833+00:00
-- url     : https://prove2.me/theorems/6408ed05-8c38-4ba1-bb7c-d4bf5239a981
-- title:
--   Kyprianou.ProofPreparation.finite_poisson_count_real_total_hasLaw
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.finite_poisson_count_real_total_hasLaw from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem finite_poisson_count_real_total_hasLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P)
    (hsum : Summable rate)
    (hfinite : ∀ᵐ w ∂P,
      (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    P.map (fun w : Omega =>
      ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) =
      (poissonMeasure ((∑' k, (rate k : ENNReal)).toNNReal)).map
        (Nat.cast : Nat -> Real) := by sorry
end Kyprianou.ProofPreparation
