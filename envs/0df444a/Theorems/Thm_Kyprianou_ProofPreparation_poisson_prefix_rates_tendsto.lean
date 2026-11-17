-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_prefix_rates_tendsto
-- name    : Kyprianou.ProofPreparation.poisson_prefix_rates_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:02.629933+00:00
-- url     : https://prove2.me/theorems/9acbd0dd-546c-4cd8-bb9e-24ee0c40bef0
-- title:
--   Kyprianou.ProofPreparation.poisson_prefix_rates_tendsto
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.poisson_prefix_rates_tendsto from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem poisson_prefix_rates_tendsto
    (rate : ℕ → ℝ≥0) (hsum : Summable rate) :
    Tendsto (fun n : ℕ => ∑ k ∈ Finset.range n, rate k)
      atTop (𝓝 ((∑' k, (rate k : ENNReal)).toNNReal)) := by sorry
end Kyprianou.ProofPreparation
