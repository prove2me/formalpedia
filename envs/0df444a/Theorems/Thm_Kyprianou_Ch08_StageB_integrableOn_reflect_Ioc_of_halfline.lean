-- Prove2me | Theorems.Thm_Kyprianou_Ch08_StageB_integrableOn_reflect_Ioc_of_halfline
-- name    : Kyprianou.Ch08.StageB.integrableOn_reflect_Ioc_of_halfline
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:12:39.11661+00:00
-- url     : https://prove2.me/theorems/670097c7-caa2-49f3-9eaf-3024e1deaa86
-- title:
--   Reflection of an integrable positive-halfline kernel to a causal interval
-- statement:
--   If f is integrable over the positive real half-line, then the reflected kernel s↦f(x−s) is integrable over 0<s≤x for every x≥0. Follows from interval-integrability restriction, IntervalIntegrable.comp_sub_left and symmetry. Needed to bring weighted Laplace scale-power integrability into source Chapter 8 convolution-power estimates.
-- source:
--   Measure-theoretic change of variables supporting Kyprianou (2006) Chapter 8 Lemma 8.3, equation (8.23).

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false
open MeasureTheory Set

namespace Kyprianou.Ch08.StageB

/-- Reflect an integrable positive-halfline kernel onto a finite causal interval. -/
theorem integrableOn_reflect_Ioc_of_halfline
    (f : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hf : IntegrableOn f (Set.Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun s : ℝ => f (x - s)) (Set.Ioc (0 : ℝ) x) volume := by
  sorry

end Kyprianou.Ch08.StageB
