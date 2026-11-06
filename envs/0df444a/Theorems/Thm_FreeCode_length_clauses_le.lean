-- Prove2me | Theorems.Thm_FreeCode_length_clauses_le
-- name    : FreeCode.length_clauses_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:48.036435+00:00
-- url     : https://prove2.me/theorems/5f8e408d-691a-4c48-be9f-580eae6cb7b3
-- title:
--   Free Code: length clauses le
-- statement:
--   The clauses of a formula with at most k literals per clause are written with at most m·(2 +
--   k·(⌊log₂ 2n⌋ + 2)) bits, m the number of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L84-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Code.lean#L84-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FreeCode_Code
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.length_clauses_le {k n : ℕ} (φ : CNF n) (h : ∀ C ∈ φ, C.length ≤ k) :
    (φ.flatMap SatFree.encClause).length ≤ φ.length * (2 + k * (Nat.log2 (2 * n) + 2)) := by sorry
