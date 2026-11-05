-- Prove2me | Theorems.Thm_Groundwork_PolyT_contains
-- name    : Groundwork.PolyT.contains
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:10.179097+00:00
-- url     : https://prove2.me/theorems/87517c6a-5132-420c-bae1-a4b4535f6156
-- title:
--   Poly T: contains
-- statement:
--   Membership in the form `contains`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L30-L32
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L30-L32

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_List2
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.ProdSigma
import Definitions.Def_ToTuring_Lib_List3
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.contains [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {b : α → β} {l : α → List β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => (l x).contains (b x)) := by sorry
