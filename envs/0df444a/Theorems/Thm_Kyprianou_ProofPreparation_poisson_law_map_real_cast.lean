-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_law_map_real_cast
-- name    : Kyprianou.ProofPreparation.poisson_law_map_real_cast
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:35.3532+00:00
-- url     : https://prove2.me/theorems/e95aa6e0-a274-422f-893e-b8566775f007
-- title:
--   Kyprianou.ProofPreparation.poisson_law_map_real_cast
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.poisson_law_map_real_cast from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem poisson_law_map_real_cast
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℕ) (r : ℝ≥0)
    (hlaw : P.map X = poissonMeasure r)
    (hX : AEMeasurable X P) :
    P.map (fun ω => (X ω : ℝ)) =
      (poissonMeasure r).map (Nat.cast : ℕ → ℝ) := by sorry
end Kyprianou.ProofPreparation
