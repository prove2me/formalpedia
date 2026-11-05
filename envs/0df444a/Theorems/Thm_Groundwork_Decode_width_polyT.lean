-- Prove2me | Theorems.Thm_Groundwork_Decode_width_polyT
-- name    : Groundwork.Decode.width_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:29:48.784797+00:00
-- url     : https://prove2.me/theorems/41058c49-7a1c-4d71-96f1-337472eeddad
-- title:
--   Decode: width poly T
-- statement:
--   The Decode construction uses the width poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Decode.lean#L21-L22
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Decode.lean#L21-L22

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_ToTuring_Poly_Decode
set_option autoImplicit false
section
section
open Groundwork Groundwork.Decode
variable {α : Type} [Enc α]

theorem Groundwork.Decode.width_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => width (n x) := by sorry
