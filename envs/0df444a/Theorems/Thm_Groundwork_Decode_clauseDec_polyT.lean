-- Prove2me | Theorems.Thm_Groundwork_Decode_clauseDec_polyT
-- name    : Groundwork.Decode.clauseDec_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:31:01.79581+00:00
-- url     : https://prove2.me/theorems/2371e4f2-7a56-4574-bd8a-2a2a9630e53e
-- title:
--   Decode: clause Dec poly T
-- statement:
--   The Decode construction uses the clause Dec poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Decode.lean#L27-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Decode.lean#L27-L29

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

theorem Groundwork.Decode.clauseDec_polyT {w : α → ℕ} {b : α → List Bool} (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => clauseDec (w x) (b x) := by sorry
