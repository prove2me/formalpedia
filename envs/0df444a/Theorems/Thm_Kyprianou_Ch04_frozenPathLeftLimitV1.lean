-- Prove2me | Theorems.Thm_Kyprianou_Ch04_frozenPathLeftLimitV1
-- name    : Kyprianou.Ch04.frozenPathLeftLimitV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:13:25.863342+00:00
-- url     : https://prove2.me/theorems/ffcdda8a-f147-5def-8b38-3515204b96ac
-- title:
--   Freezing preserves strict left limits before or at the horizon
-- statement:
--   The frozen and original functions agree eventually on the strict left neighbourhood.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, physical predictable integral approximation.

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem frozenPathLeftLimitV1 (Y : NNReal → ℝ) (T u : NNReal) (l : ℝ)
    (hu : u ≤ T) (hL : Tendsto Y (𝓝[<] u) (𝓝 l)) :
    Tendsto (fun v => Y (min v T)) (𝓝[<] u) (𝓝 l) := by
  sorry
end Kyprianou.Ch04
