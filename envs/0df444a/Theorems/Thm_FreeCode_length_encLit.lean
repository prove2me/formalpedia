-- Prove2me | Theorems.Thm_FreeCode_length_encLit
-- name    : FreeCode.length_encLit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:39:33.881789+00:00
-- url     : https://prove2.me/theorems/a8d10e7d-0a0f-4deb-8b78-0374286af11f
-- title:
--   Free Code: length enc Lit
-- statement:
--   A literal is written with ⌊log₂ 2n⌋ + 1 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L64-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L64-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.length_encLit {n : ℕ} (l : Lit n) : (SatFree.encLit l).length = Nat.log2 (2 * n) + 1 := by sorry
