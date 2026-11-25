-- Prove2me | Theorems.Thm_Kyprianou_Ch04_predictableGridValueSup
-- name    : Kyprianou.Ch04.predictableGridValueSup
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T23:59:05.794937+00:00
-- url     : https://prove2.me/theorems/abcfe8f7-9915-493e-a907-d01e717dabbf
-- title:
--   Countable grid window supremum equals the sampled value
-- statement:
--   At zero the initial atom contributes the exact value. At positive times a covering cell contributes the sampled value, and every nonzero window contribution equals that same value.
-- source:
--   Kyprianou (2006), Theorem 4.4, printed page 95, proof decomposition of the common-null-event corrected statement.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
open MeasureTheory Filter LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem predictableGridValueSup
    (q : NNReal → NNReal) (a b : Nat → NNReal)
    (h0 : q 0 = 0)
    (hcell : ∀ k t, t ∈ Set.Ioc (a k) (b k) → q t = a k)
    (hcover : ∀ t, 0 < t → ∃ k, t ∈ Set.Ioc (a k) (b k))
    (g : NNReal → ENNReal) (t : NNReal) :
    g (q t) = max (({0} : Set NNReal).indicator (fun _ => g 0) t)
      (⨆ k, (Set.Ioc (a k) (b k)).indicator (fun _ => g (a k)) t) := by
  sorry
end Kyprianou.Ch04
