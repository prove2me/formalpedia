-- Prove2me | Theorems.Thm_Groundwork_DecodeK_clauseDec_polyT
-- name    : Groundwork.DecodeK.clauseDec_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:01:39.017231+00:00
-- url     : https://prove2.me/theorems/01c7f724-3613-46ed-ba5e-19e449c7f0d9
-- title:
--   Decode K: clause Dec poly T
-- statement:
--   Reading one clause from a block of k slots of w bits is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Poly/Decode.lean#L26-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/WidthK/Poly/Decode.lean#L26-L28

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_WidthK_Decode
import Definitions.Def_WidthK_Poly_Decode
import Theorems.Thm_Groundwork_Decode_clauseDec_polyT
attribute [local fun_prop] Groundwork.Decode.clauseDec_polyT


set_option autoImplicit false
section
section
open Groundwork Groundwork.DecodeK
open Groundwork.Decode
variable {α : Type} [Enc α]

theorem Groundwork.DecodeK.clauseDec_polyT (k : ℕ) {w : α → ℕ} {b : α → List Bool} (hw : PolyT w) (hb : PolyT b) :
    PolyT fun x => clauseDec k (w x) (b x) := by sorry
