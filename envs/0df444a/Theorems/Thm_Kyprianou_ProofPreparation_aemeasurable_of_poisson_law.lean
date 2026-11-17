-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_aemeasurable_of_poisson_law
-- name    : Kyprianou.ProofPreparation.aemeasurable_of_poisson_law
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:39.604067+00:00
-- url     : https://prove2.me/theorems/4962ea2d-d33c-4307-9d40-fc691164d43b
-- title:
--   Kyprianou.ProofPreparation.aemeasurable_of_poisson_law
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.aemeasurable_of_poisson_law from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem aemeasurable_of_poisson_law
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (r : ℝ≥0) (N : Ω → ℕ)
    (hlaw : P.map N = poissonMeasure r) :
    AEMeasurable N P := by sorry
end Kyprianou.ProofPreparation
