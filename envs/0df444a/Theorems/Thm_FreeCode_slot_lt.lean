-- Prove2me | Theorems.Thm_FreeCode_slot_lt
-- name    : FreeCode.slot_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:26:37.857864+00:00
-- url     : https://prove2.me/theorems/5ba24f9c-4db8-404c-a586-5526443ad1a7
-- title:
--   Free Code: slot lt
-- statement:
--   The number of a literal on n variables is below 2^(⌊log₂ 2n⌋+1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L44-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L44-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_Groundwork_Decode_slot_lt

set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.slot_lt {n : ℕ} (l : Lit n) : slot (some l) < 2 ^ (Nat.log2 (2 * n) + 1) := by sorry
