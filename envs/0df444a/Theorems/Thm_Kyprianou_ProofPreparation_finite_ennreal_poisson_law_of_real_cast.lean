-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_finite_ennreal_poisson_law_of_real_cast
-- name    : Kyprianou.ProofPreparation.finite_ennreal_poisson_law_of_real_cast
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:34.998733+00:00
-- url     : https://prove2.me/theorems/6c595f77-10cb-40d0-9a94-06d03f116be3
-- title:
--   Kyprianou.ProofPreparation.finite_ennreal_poisson_law_of_real_cast
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.finite_ennreal_poisson_law_of_real_cast from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem finite_ennreal_poisson_law_of_real_cast
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (S : Omega -> ENNReal) (rate : NNReal)
    (hS : AEMeasurable S P)
    (hfinite : ∀ᵐ w ∂P, S w < ⊤)
    (hreal :
      P.map (fun w => (S w).toReal) =
        (poissonMeasure rate).map (Nat.cast : Nat -> Real)) :
    P.map S = (poissonMeasure rate).map (Nat.cast : Nat -> ENNReal) := by sorry
end Kyprianou.ProofPreparation
