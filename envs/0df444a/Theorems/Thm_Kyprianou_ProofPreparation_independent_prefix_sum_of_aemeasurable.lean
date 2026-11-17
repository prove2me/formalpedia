-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_independent_prefix_sum_of_aemeasurable
-- name    : Kyprianou.ProofPreparation.independent_prefix_sum_of_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:42.683209+00:00
-- url     : https://prove2.me/theorems/82e14047-990f-42d7-87d0-e2970a5673fe
-- title:
--   Kyprianou.ProofPreparation.independent_prefix_sum_of_aemeasurable
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.independent_prefix_sum_of_aemeasurable from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem independent_prefix_sum_of_aemeasurable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω)
    (N : ℕ → Ω → ℕ)
    (hind : iIndepFun N P)
    (hN : ∀ k, AEMeasurable (N k) P)
    (s : Finset ℕ) (k : ℕ) (hk : k ∉ s) :
    IndepFun (fun ω => ∑ j ∈ s, N j ω) (N k) P := by sorry
end Kyprianou.ProofPreparation
