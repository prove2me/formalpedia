-- Prove2me | Theorems.Thm_Groundwork_PolyT_elem
-- name    : Groundwork.PolyT.elem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:27:41.875282+00:00
-- url     : https://prove2.me/theorems/c6245fc9-1197-4f5c-89ff-d21072698b38
-- title:
--   Poly T: elem
-- statement:
--   Membership in the form `elem`. The test `==` may be any lawful one: on pairs, options and lists
--   it is not the one made
--   from `DecidableEq`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L24-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List3.lean#L24-L27

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

theorem Groundwork.PolyT.elem [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {b : α → β} {l : α → List β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => (l x).elem (b x)) := by sorry
