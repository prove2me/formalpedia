-- Prove2me | Theorems.Thm_Groundwork_DecodeK_clauses_polyT
-- name    : Groundwork.DecodeK.clauses_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:07:39.069999+00:00
-- url     : https://prove2.me/theorems/ab62c9e6-8459-4e9a-8ac8-44abc4d23922
-- title:
--   Decode K: clauses poly T
-- statement:
--   Reading the list of clauses from the body b of the input, one block of k·w bits per clause, is
--   polynomial-time. This is the
--   second component of `decK k`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Poly/Decode.lean#L33-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Poly/Decode.lean#L33-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_WidthK_Poly_Decode
import Theorems.Thm_Groundwork_Decode_clauses_polyT
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open Groundwork Groundwork.DecodeK
open Groundwork.Decode
variable {α : Type} [Enc α]

theorem Groundwork.DecodeK.clauses_polyT (k : ℕ) {w : α → ℕ} {b : α → List Bool} (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => ((List.range (b x).length).take ((b x).length / (k * w x))).map fun c =>
      clauseDec k (w x) (block (k * w x) c (b x)) := by sorry
