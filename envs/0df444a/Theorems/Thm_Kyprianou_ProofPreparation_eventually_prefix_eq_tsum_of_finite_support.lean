-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_eventually_prefix_eq_tsum_of_finite_support
-- name    : Kyprianou.ProofPreparation.eventually_prefix_eq_tsum_of_finite_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:50.871391+00:00
-- url     : https://prove2.me/theorems/630bef9b-314a-4d8d-994e-369b8c5a7b72
-- title:
--   Kyprianou.ProofPreparation.eventually_prefix_eq_tsum_of_finite_support
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.eventually_prefix_eq_tsum_of_finite_support from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem eventually_prefix_eq_tsum_of_finite_support
    (N : ℕ → ℕ) (hfinite : Set.Finite {k : ℕ | N k ≠ 0}) :
    ∃ n : ℕ, ∀ m ≥ n,
      (∑' k, (N k : ENNReal)) =
        ∑ k ∈ Finset.range m, (N k : ENNReal) := by sorry
end Kyprianou.ProofPreparation
