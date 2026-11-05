-- Prove2me | Theorems.Thm_Groundwork_Decode_clauses_polyT
-- name    : Groundwork.Decode.clauses_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:30:18.994489+00:00
-- url     : https://prove2.me/theorems/12a478f8-91a3-4c56-8451-b8102297e8c8
-- title:
--   Decode: clauses poly T
-- statement:
--   Reading the list of clauses from the body b of the input, one block of 3·w bits per clause, is
--   polynomial-time. This is the
--   second component of `dec`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Decode.lean#L34-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/Decode.lean#L34-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Groundwork Groundwork.Decode
variable {α : Type} [Enc α]

theorem Groundwork.Decode.clauses_polyT {w : α → ℕ} {b : α → List Bool} (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => ((List.range (b x).length).take ((b x).length / (3 * w x))).map fun c =>
      clauseDec (w x) (block (3 * w x) c (b x)) := by sorry
