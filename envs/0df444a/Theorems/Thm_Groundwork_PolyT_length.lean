-- Prove2me | Theorems.Thm_Groundwork_PolyT_length
-- name    : Groundwork.PolyT.length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:01.001637+00:00
-- url     : https://prove2.me/theorems/77da38c7-a10d-4b3b-8230-72f59c242430
-- title:
--   Poly T: length
-- statement:
--   The length of a list, in binary: a fold that adds 1 for every element.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L84-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L84-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Nat1
import Definitions.Def_ToTuring_Lib_Nat1b
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.length {l : α → List β} (hl : PolyT l) :
    PolyT (fun x => (l x).length) := by sorry
