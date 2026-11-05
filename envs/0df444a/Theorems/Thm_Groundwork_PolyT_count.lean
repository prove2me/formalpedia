-- Prove2me | Theorems.Thm_Groundwork_PolyT_count
-- name    : Groundwork.PolyT.count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:30.948061+00:00
-- url     : https://prove2.me/theorems/6c05f7a9-67f8-411b-a071-962382153919
-- title:
--   Poly T: count
-- statement:
--   The number of occurrences of an element: `countP` with the test of equality (`BEq` as for
--   `PolyT.beq'`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L147-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L147-L151

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

theorem Groundwork.PolyT.count [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {l : α → List β} {b : α → β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => (l x).count (b x)) := by sorry
