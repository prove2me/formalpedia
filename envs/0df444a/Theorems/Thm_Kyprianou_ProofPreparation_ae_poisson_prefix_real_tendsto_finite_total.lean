-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_ae_poisson_prefix_real_tendsto_finite_total
-- name    : Kyprianou.ProofPreparation.ae_poisson_prefix_real_tendsto_finite_total
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:43.868688+00:00
-- url     : https://prove2.me/theorems/463cb8d2-7f6b-4541-af05-fda2cbdbb9a8
-- title:
--   Kyprianou.ProofPreparation.ae_poisson_prefix_real_tendsto_finite_total
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.ae_poisson_prefix_real_tendsto_finite_total from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem ae_poisson_prefix_real_tendsto_finite_total
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (N : Nat -> Omega -> Nat)
    (hfinite : ∀ᵐ w ∂P,
        (∑' k, ((N k w : Nat) : ENNReal)) < ⊤) :
    ∀ᵐ w ∂P,
      Tendsto
        (fun n : Nat => (((∑ k ∈ Finset.range n, N k w) : Nat) : Real))
        atTop
        (𝓝 ((∑' k, ((N k w : Nat) : ENNReal)) : ENNReal).toReal) := by sorry
end Kyprianou.ProofPreparation
