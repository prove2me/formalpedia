-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_marginal_lintegral
-- name    : Kyprianou.ProofPreparation.poisson_marginal_lintegral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:29.119686+00:00
-- url     : https://prove2.me/theorems/3f2dcf44-b767-4868-a014-f410aeb9bf13
-- title:
--   Kyprianou.ProofPreparation.poisson_marginal_lintegral
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.poisson_marginal_lintegral from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem poisson_marginal_lintegral
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (X : Omega -> Nat) (r : NNReal)
    (hX : P.map X = poissonMeasure r) :
    (∫⁻ w, ((X w : Nat) : ENNReal) ∂P) = (r : ENNReal) := by sorry
end Kyprianou.ProofPreparation
