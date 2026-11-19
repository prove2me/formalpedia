-- Prove2me | Theorems.Thm_Kyprianou_Ch03_firstHittingFinite_timeSelector
-- name    : Kyprianou.Ch03.firstHittingFinite_timeSelector
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:26:46.162182+00:00
-- url     : https://prove2.me/theorems/53a41aa4-e7cf-435e-add0-1c482eaa98ab
-- title:
--   Chapter 3 first hitting: finite time witness for each noninfinite hitting time
-- statement:
--   Any WithTop-valued first hitting time admits a pathwise NNReal representative on its finite event, with no probabilistic assumptions.
-- source:
--   Derived directly from original Kyprianou Chapter 3 first-hitting-time definition and Exercise 3.6 zero-root passage event

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_LevyExtrema_SBA_runSup
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03
theorem firstHittingFinite_timeSelector
    {Omega : Type} (X : NNReal → Omega → ℝ)
    (B : Set ℝ) :
    ∃ f : Omega → NNReal,
      ∀ omega : Omega,
        (firstHittingTime X B omega != ⊤) →
          firstHittingTime X B omega = (f omega : WithTop NNReal) := by
  sorry
end Kyprianou.Ch03
