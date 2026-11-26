-- Prove2me | Theorems.Thm_O3_stage9_pairing_summation_by_parts
-- name    : O3.stage9_pairing_summation_by_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:26:31.280043+00:00
-- url     : https://prove2.me/theorems/ddd8b536-029d-59b4-a016-ab98f3d7d85c
-- title:
--   O3: stage9 pairing summation by parts
-- statement:
--   Discrete summation by parts for the second pairing sum in the frozen
--   certificate.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L52-L98
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/Stage9Telescoping.lean#L52-L98

import Definitions.Def_O3_Foundation
import Definitions.Def_O3_Stage2RouteC
import Definitions.Def_O3_Stage2RouteD
import Definitions.Def_O3_Stage9Telescoping
set_option autoImplicit true
open scoped BigOperators
open O3

theorem O3.stage9_pairing_summation_by_parts {d : ℕ}
    (delta : ℕ → ℝ) (g v : ℕ → Vec d) : ∀ n,
    (∑ i ∈ Finset.range n,
        delta i * pairing (g i) (v n - v i)) =
      ∑ k ∈ Finset.range n,
        pairing (stage9WeightedGradient delta g (k + 1))
          (v (k + 1) - v k) := by sorry
