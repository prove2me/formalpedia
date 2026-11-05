-- Prove2me | Theorems.Thm_Groundwork_PolyT_pow_unary
-- name    : Groundwork.PolyT.pow_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:08.657386+00:00
-- url     : https://prove2.me/theorems/20b86a8b-52bf-44cd-8239-54ed70e57e4f
-- title:
--   Poly T: pow unary
-- statement:
--   A power is polynomial-time if its exponent can be written in unary: every round makes the word
--   longer by at most the
--   length of the word of the base.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L187-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L187-L197

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

theorem Groundwork.PolyT.pow_unary {b e : α → ℕ} (hb : PolyT b) (he : Unary e) :
    PolyT (fun x => b x ^ e x) := by sorry
