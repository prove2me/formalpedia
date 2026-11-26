-- Prove2me | Theorems.Thm_O3_Experimental_scalarJ_strongMonotone_ordered
-- name    : O3.Experimental.scalarJ_strongMonotone_ordered
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:54:18.216128+00:00
-- url     : https://prove2.me/theorems/56be8c38-ef26-46b6-a18e-6a4ab6f4d999
-- title:
--   Experimental: scalar J strong Monotone ordered
-- statement:
--   The Experimental construction uses the scalar J strong Monotone ordered property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L25-L112
-- source:
--   https://github.com/yuningyang19/parameter_free_gradient_p/blob/f71215fa936fe01aff8a765c62b399e131df963b/O3/GeometryExperimental.lean#L25-L112

import Definitions.Def_O3_Geometry
import Definitions.Def_O3_GeometryExperimental
set_option autoImplicit true
open O3 O3.Experimental

theorem O3.Experimental.scalarJ_strongMonotone_ordered {p u v : ℝ} (hp : 2 < p) (huv : v ≤ u) :
    (2 : ℝ) ^ (2 - p) * |u - v| ^ p ≤ (scalarJ p u - scalarJ p v) * (u - v) := by sorry
