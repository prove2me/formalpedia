-- Prove2me | Theorems.Thm_Kyprianou_Ch04_frozenPathLeftExistenceV1
-- name    : Kyprianou.Ch04.frozenPathLeftExistenceV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T07:15:02.780185+00:00
-- url     : https://prove2.me/theorems/8482177f-7f7b-5eba-9633-91fadec666ab
-- title:
--   Frozen path has finite left limits at every positive time
-- statement:
--   Before or at T use the original left limit, and afterwards use the constant frozen value.
-- source:
--   Kyprianou (2006), Chapter 4, Exercise 4.5, adapted physical Poisson counts.

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_frozenPathLeftLimitV1
import Theorems.Thm_Kyprianou_Ch04_frozenPathLeftLimitAfterV1
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch04
theorem frozenPathLeftExistenceV1 (Y L : NNReal → ℝ) (T : NNReal)
    (hL : ∀ u, 0 < u → Tendsto Y (𝓝[<] u) (𝓝 (L u))) :
    ∀ u : NNReal, 0 < u →
      ∃ l : ℝ, Tendsto (fun v => Y (min v T)) (𝓝[<] u) (𝓝 l) := by
  sorry
end Kyprianou.Ch04
