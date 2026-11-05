-- Prove2me | Theorems.Thm_Groundwork_PolyT_two_pow
-- name    : Groundwork.PolyT.two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:38:41.572731+00:00
-- url     : https://prove2.me/theorems/dbbb966a-611d-4305-84a2-ebd3518cc5f7
-- title:
--   Poly T: two pow
-- statement:
--   The case of `pow_unary` with base 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L200-L202
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L200-L202

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.two_pow {e : α → ℕ} (he : Unary e) :
    PolyT (fun x => 2 ^ e x) := by sorry
