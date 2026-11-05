-- Prove2me | Theorems.Thm_Groundwork_PolyT_unary_min_length
-- name    : Groundwork.PolyT.unary_min_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:08:26.489719+00:00
-- url     : https://prove2.me/theorems/f2ef84c9-823f-497f-a3d5-c697ef338436
-- title:
--   Poly T: unary min length
-- statement:
--   The smaller of a number in binary and the length of a list can be written in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L223-L235
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L223-L235

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.unary_min_length {q : α → ℕ} {l : α → List β} (hq : PolyT q) (hl : PolyT l) :
    Unary (fun x => min (q x) (l x).length) := by sorry
