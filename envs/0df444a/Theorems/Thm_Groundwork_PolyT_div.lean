-- Prove2me | Theorems.Thm_Groundwork_PolyT_div
-- name    : Groundwork.PolyT.div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:38:34.568607+00:00
-- url     : https://prove2.me/theorems/be1bd4c7-f8b6-4c53-ad40-f230451bcee8
-- title:
--   Poly T: div
-- statement:
--   The quotient is polynomial-time; the divisor 0 is a separate case (the quotient is then 0).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L146-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat2.lean#L146-L154

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

theorem Groundwork.PolyT.div {f g : α → ℕ} (hf : PolyT f) (hg : PolyT g) :
    PolyT (fun x => f x / g x) := by sorry
