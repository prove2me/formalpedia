-- Prove2me | Theorems.Thm_Kyprianou_ProofPreparation_poisson_charfun_continuous_in_rate
-- name    : Kyprianou.ProofPreparation.poisson_charfun_continuous_in_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-16T22:30:50.375095+00:00
-- url     : https://prove2.me/theorems/2d9c2a3a-7ef7-4c42-b250-8091ca9ec1dd
-- title:
--   Kyprianou.ProofPreparation.poisson_charfun_continuous_in_rate
-- statement:
--   Automatically extracted helper theorem Kyprianou.ProofPreparation.poisson_charfun_continuous_in_rate from oversized parent candidate 81a258adc97c4344f640c13016c61161d02554f5de4b4ab7ab8267bce3298d43.
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
theorem poisson_charfun_continuous_in_rate
    (rate : ℕ → ℝ≥0) (r : ℝ≥0)
    (hrate : Tendsto rate atTop (𝓝 r)) (t : ℝ) :
    Tendsto (fun n => charFun ((poissonMeasure (rate n)).map
      (Nat.cast : ℕ → ℝ)) t)
      atTop (𝓝 (charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) t)) := by sorry
end Kyprianou.ProofPreparation
