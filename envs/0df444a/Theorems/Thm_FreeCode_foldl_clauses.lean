-- Prove2me | Theorems.Thm_FreeCode_foldl_clauses
-- name    : FreeCode.foldl_clauses
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:20.364734+00:00
-- url     : https://prove2.me/theorems/486c7543-183c-4590-b9c3-aa4018166a2d
-- title:
--   Free Code: foldl clauses
-- statement:
--   Between clauses: the codes of the clauses of φ put them on the list of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L119-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L119-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Mathlib.Tactic
import Definitions.Def_FreeCode_Reader
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.foldl_clauses {n : ℕ} : ∀ (φ : CNF n) (acc : List (List (List Bool))),
    (φ.flatMap SatFree.encClause).foldl (stepR (Nat.log2 (2 * n) + 1)) (false, false, [], [], acc) =
      (false, false, [], [], (φ.map fun C => (C.map fun l => (SatFree.encLit l).reverse).reverse).reverse ++ acc)
  := by sorry
