-- Prove2me | Theorems.Thm_Groundwork_PolyT_countP
-- name    : Groundwork.PolyT.countP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:20.993255+00:00
-- url     : https://prove2.me/theorems/89c04bc3-6d09-4605-b6e7-8b91ac2728b5
-- title:
--   Poly T: count P
-- statement:
--   The number of elements that pass a test: the length of the filtered list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L141-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L141-L143

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

theorem Groundwork.PolyT.countP {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).countP (f x)) := by sorry
