-- Prove2me | Theorems.Thm_FreeCode_toWord_eq
-- name    : FreeCode.toWord_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:25.186118+00:00
-- url     : https://prove2.me/theorems/b8c9ed87-14f6-4714-918e-c022ff9ff2d3
-- title:
--   Free Code: to Word eq
-- statement:
--   The ℓ lowest binary digits of y, lowest first, are its bits number 0 to ℓ − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L33-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L33-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_Groundwork_Decode_toWord_eq
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.toWord_eq (ℓ y : ℕ) : toWord ℓ y = (List.range ℓ).map y.testBit := by sorry
