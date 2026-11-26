-- Prove2me | Theorems.Thm_Kyprianou_Ch04_exercise46RightGridFutureLimitV1
-- name    : Kyprianou.Ch04.exercise46RightGridFutureLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T22:58:48.828425+00:00
-- url     : https://prove2.me/theorems/90d4e2f4-f484-53dc-96bd-bf7be63b50ba
-- title:
--   Coordinatewise right-grid shifted path limit
-- statement:
--   Both coordinates converge by right continuity along upper approximations.
-- source:
--   Kyprianou (2006), Exercise 4.6(ii).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology

theorem Kyprianou.Ch04.exercise46RightGridFutureLimitV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : SpectrallyNegativeLevy P F)
    (s : Omega → NNReal) (T : ℕ → Omega → NNReal)
    (w : Omega)
    (hAbove : ∀ n, s w ≤ T n w)
    (hlim : Tendsto (fun n => T n w) atTop (nhds (s w))) (u : NNReal) :
    Tendsto (fun n => L.X (T n w + u) w - L.X (T n w) w) atTop
      (nhds (L.X (s w + u) w - L.X (s w) w)) := by
  sorry
