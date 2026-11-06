-- Prove2me | Theorems.Thm_FreeCode_length_encClause
-- name    : FreeCode.length_encClause
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:55.294048+00:00
-- url     : https://prove2.me/theorems/ed2fd097-aea2-4bea-a7ea-82d713403037
-- title:
--   Free Code: length enc Clause
-- statement:
--   A clause of s literals is written with 2 + s·(⌊log₂ 2n⌋ + 2) bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L72-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L72-L80

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

theorem FreeCode.length_encClause {n : ℕ} (C : List (Lit n)) : (SatFree.encClause C).length = 2 + C.length * (Nat.log2 (2 * n) + 2) := by sorry
