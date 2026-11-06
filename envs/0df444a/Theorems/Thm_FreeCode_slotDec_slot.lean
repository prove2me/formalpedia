-- Prove2me | Theorems.Thm_FreeCode_slotDec_slot
-- name    : FreeCode.slotDec_slot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:15.107198+00:00
-- url     : https://prove2.me/theorems/7cc8d6a1-5261-4f6e-8628-eed58eb1c6f5
-- title:
--   Free Code: slot Dec slot
-- statement:
--   The number of a literal, read as a literal, gives the literal back, with its variable as a
--   number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L52-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L52-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_Groundwork_Decode_slotDec_slot

set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.slotDec_slot {n : ℕ} (l : Lit n) : slotDec (slot (some l)) = some (l.1.val, l.2) := by sorry
