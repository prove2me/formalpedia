-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_finite_poisson_prefix_real_tendstoInDistribution
-- name    : Kyprianou.ProofPreparation.finite_poisson_prefix_real_tendstoInDistribution
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:52.293444+00:00
-- url     : https://prove2.me/theorems/95d8b8de-b357-4fed-ac31-37fbb5ebb5e1
-- title:
--   Kyprianou.ProofPreparation.finite_poisson_prefix_real_tendstoInDistribution
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.finite_poisson_prefix_real_tendstoInDistribution from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem finite_poisson_prefix_real_tendstoInDistribution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (N : Nat -> Omega -> Nat)
    (hN : forall k, AEMeasurable (N k) P)
    (hfinite : ∀ᵐ w ∂P,
       (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    TendstoInDistribution
      (fun n (w : Omega) =>
        (((∑ k ∈ Finset.range n, N k w) : Nat) : Real))
      atTop (fun w : Omega =>
        ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal)
      (fun _ => P) P := by sorry
end Kyprianou.ProofPreparation
