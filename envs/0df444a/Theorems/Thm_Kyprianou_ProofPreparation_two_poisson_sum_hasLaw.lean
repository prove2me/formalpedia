-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_two_poisson_sum_hasLaw
-- name    : Kyprianou.ProofPreparation.two_poisson_sum_hasLaw
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:31:06.775411+00:00
-- url     : https://prove2.me/theorems/7f2dca50-ef5e-40ad-8aeb-58ce58001ca9
-- title:
--   Kyprianou.ProofPreparation.two_poisson_sum_hasLaw
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.two_poisson_sum_hasLaw from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem two_poisson_sum_hasLaw
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (r₁ r₂ : ℝ≥0) (X Y : Ω → ℕ)
    (hX : P.map X = poissonMeasure r₁)
    (hY : P.map Y = poissonMeasure r₂)
    (hi : IndepFun X Y P) :
    P.map (fun ω => X ω + Y ω) = poissonMeasure (r₁ + r₂) := by sorry
end Kyprianou.ProofPreparation
