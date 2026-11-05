-- Prove2me | Theorems.Thm_Groundwork_PolyT_idxOf
-- name    : Groundwork.PolyT.idxOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:32.7872+00:00
-- url     : https://prove2.me/theorems/dfff7574-a42d-4cfe-b8b1-137581d4148a
-- title:
--   Poly T: idx Of
-- statement:
--   The index of the first occurrence of an element (the length of the list if there is none): a
--   fold from the right (`BEq` as
--   for `PolyT.beq'`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L156-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/Nat1b.lean#L156-L171

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

theorem Groundwork.PolyT.idxOf [DecidableEq β] [EqT β] [BEq β] [LawfulBEq β] {l : α → List β} {b : α → β} (hb : PolyT b)
    (hl : PolyT l) : PolyT (fun x => (l x).idxOf (b x)) := by sorry
