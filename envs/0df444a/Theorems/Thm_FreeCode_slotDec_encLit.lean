-- Prove2me | Theorems.Thm_FreeCode_slotDec_encLit
-- name    : FreeCode.slotDec_encLit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:25:34.330217+00:00
-- url     : https://prove2.me/theorems/0afd6f4d-a48a-4b7a-ba0f-9ed777609966
-- title:
--   Free Code: slot Dec enc Lit
-- statement:
--   The bits of a literal, read as a number and then as a literal, give the literal back.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L68-L69
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L68-L69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.slotDec_encLit {n : ℕ} (l : Lit n) : slotDec (ofWord (SatFree.encLit l)) = some (l.1.val, l.2) := by sorry
