-- Prove2me | Theorems.Thm_Groundwork_Unary_of_length
-- name    : Groundwork.Unary.of_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:29:39.083557+00:00
-- url     : https://prove2.me/theorems/dcf5855a-8ed5-4d59-b380-fbd6a6a449ff
-- title:
--   Unary: of length
-- statement:
--   The length of a polynomial-time list is polynomial-time in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L31-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Unary.lean#L31-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Unary
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Groundwork Groundwork.Unary
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]
variable {f g : α → ℕ}

theorem Groundwork.Unary.of_length {w : α → List γ} (hw : PolyT w) :
    Unary fun c => (w c).length := by sorry
