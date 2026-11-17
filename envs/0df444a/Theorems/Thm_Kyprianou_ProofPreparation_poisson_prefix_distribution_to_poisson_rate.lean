-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_distribution_to_poisson_rate
-- name    : Kyprianou.ProofPreparation.poisson_prefix_distribution_to_poisson_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:13.280359+00:00
-- url     : https://prove2.me/theorems/aa102006-73de-424d-8cf7-e391a435c8bd
-- title:
--   Kyprianou.ProofPreparation.poisson_prefix_distribution_to_poisson_rate
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.poisson_prefix_distribution_to_poisson_rate from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem poisson_prefix_distribution_to_poisson_rate
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (rate : Nat -> NNReal) (N : Nat -> Omega -> Nat)
    (hlaw : forall k, P.map (N k) = poissonMeasure (rate k))
    (hind : iIndepFun N P) (hsum : Summable rate) :
    TendstoInDistribution
      (fun n (w : Omega) =>
        (((∑ k ∈ Finset.range (n + 1), N k w) : Nat) : Real))
      atTop (Nat.cast : Nat -> Real) (fun _ => P)
      (poissonMeasure ((∑' k, (rate k : ENNReal)).toNNReal)) := by sorry
end Kyprianou.ProofPreparation
