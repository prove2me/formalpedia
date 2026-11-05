-- Prove2me | Theorems.Thm_Groundwork_Unary_poly
-- name    : Groundwork.Unary.poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:49.483732+00:00
-- url     : https://prove2.me/theorems/60ff4cba-4d22-45c0-8329-7dbba57bf0b0
-- title:
--   Unary: poly
-- statement:
--   A function that is polynomial-time in unary is polynomial-time as a number: take the length of
--   the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L26-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L26-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}

theorem Groundwork.Unary.poly (hf : Unary f) :
    PolyT f := by sorry
