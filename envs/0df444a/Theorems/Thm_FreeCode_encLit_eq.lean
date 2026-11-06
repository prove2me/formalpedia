-- Prove2me | Theorems.Thm_FreeCode_encLit_eq
-- name    : FreeCode.encLit_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:24:54.722895+00:00
-- url     : https://prove2.me/theorems/27763d3c-5721-4ebc-baa4-5a37e67fa097
-- title:
--   Free Code: enc Lit eq
-- statement:
--   The bits of a literal are the ⌊log₂ 2n⌋ + 1 lowest binary digits of its number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L60-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L60-L61

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

theorem FreeCode.encLit_eq {n : ℕ} (l : Lit n) : SatFree.encLit l = toWord (Nat.log2 (2 * n) + 1) (slot (some l)) := by sorry
