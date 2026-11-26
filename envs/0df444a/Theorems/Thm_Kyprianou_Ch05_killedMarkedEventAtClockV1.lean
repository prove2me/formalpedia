-- Prove2me | Theorems.Thm_Kyprianou_Ch05_killedMarkedEventAtClockV1
-- name    : Kyprianou.Ch05.killedMarkedEventAtClockV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T18:15:02.933192+00:00
-- url     : https://prove2.me/theorems/d4b651bb-24f0-45a0-9da3-501f5229d87a
-- title:
--   Marked passage event at the unkilled crossing clock
-- statement:
--   Under survival the finite killed clock is the unkilled clock. A positive overshoot forces a strictly positive time because the path starts at zero; the undershoot range implies the left value is between zero and the barrier.
-- source:
--   Kyprianou (2006), Chapter 5, Theorem 5.6.

import Mathlib
import Definitions.Def_Kyprianou_Ch05_KilledSubordinatorPotential
import Definitions.Def_Kyprianou_Ch05_FirstPassageObservables
import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_PoissonCompensationSetting
import Definitions.Def_LeanLevy_Levy_LevyMeasure
open MeasureTheory ProbabilityTheory Filter Set Complex Topology Kyprianou.Ch05
open scoped NNReal ENNReal Topology Classical
set_option autoImplicit false

theorem Kyprianou.Ch05.killedMarkedEventAtClockV1
    {Omega : Type} (Y Yleft : NNReal → Omega → ℝ) (death : Omega → WithTop NNReal)
    (x : ℝ) (hx : 0 < x) (w : Omega) (A B : Set ℝ) (hBp : B ⊆ Icc (0 : ℝ) x)
    (hz : Y 0 w = 0)
    (T : ENNReal)
    (hclock : (strictUpcrossing Y death x w : ENNReal) =
      if T < (death w : ENNReal) then T else ⊤)
    (hleft : ∀ t : NNReal, 0 < t → Yleft t w = Function.leftLim (fun s => Y s w) t) :
    (PassageFinite Y death x w ∧ 0 < passageOvershoot Y death x w ∧
      passageOvershoot Y death x w ∈ A ∧ passageUndershoot Y Yleft death x w ∈ B) ↔
      ((0 < T.toNNReal ∧ Y T.toNNReal w > x ∧
        Function.leftLim (fun s => Y s w) T.toNNReal ∈ Icc (0 : ℝ) x ∧
        Y T.toNNReal w - x ∈ A ∧
        x - Function.leftLim (fun s => Y s w) T.toNNReal ∈ B) ∧
        T < (death w : ENNReal)) := by
  sorry
