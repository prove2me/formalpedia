-- Prove2me | Theorems.Thm_Groundwork_PolyT_all
-- name    : Groundwork.PolyT.all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:34:29.013793+00:00
-- url     : https://prove2.me/theorems/cc2e4a1d-30b1-42fa-9296-5ba38419fa06
-- title:
--   Poly T: all
-- statement:
--   The Poly T construction uses the all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L128-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Lib/List1.lean#L128-L137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Lib_Bool
import Definitions.Def_ToTuring_Lib_List1
set_option autoImplicit false
section
section
open Groundwork Groundwork.PolyT
variable {α β γ δ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc δ] [Enc ε]

theorem Groundwork.PolyT.all {f : α → β → Bool} {l : α → List β} (hf : PolyT fun p : α × β => f p.1 p.2) (hl : PolyT l) :
    PolyT (fun x => (l x).all (f x)) := by sorry
