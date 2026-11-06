-- Prove2me | Theorems.Thm_FreeCode_foldl_clause
-- name    : FreeCode.foldl_clause
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:17.367093+00:00
-- url     : https://prove2.me/theorems/d71484a9-34d4-4909-8a5f-26e84627829a
-- title:
--   Free Code: foldl clause
-- statement:
--   Between clauses: the code of a clause puts the clause on the list of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L111-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L111-L116

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Mathlib.Tactic
import Definitions.Def_FreeCode_Reader
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.foldl_clause {n : ℕ} (acc : List (List (List Bool))) (C : List (Lit n)) :
    (SatFree.encClause C).foldl (stepR (Nat.log2 (2 * n) + 1)) (false, false, [], [], acc) =
      (false, false, [], [], (C.map fun l => (SatFree.encLit l).reverse).reverse :: acc) := by sorry
