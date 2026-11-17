-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_finite_nonzero_indices_of_finite_count_sum
-- name    : Kyprianou.ProofPreparation.finite_nonzero_indices_of_finite_count_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:48.853227+00:00
-- url     : https://prove2.me/theorems/b544c686-76ef-453c-8114-3dc8929cf97c
-- title:
--   Kyprianou.ProofPreparation.finite_nonzero_indices_of_finite_count_sum
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.finite_nonzero_indices_of_finite_count_sum from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem finite_nonzero_indices_of_finite_count_sum
    (N : ℕ → ℕ)
    (hfin : (∑' k, (N k : ENNReal)) < ⊤) :
    Set.Finite {k : ℕ | N k ≠ 0} := by sorry
end Kyprianou.ProofPreparation
