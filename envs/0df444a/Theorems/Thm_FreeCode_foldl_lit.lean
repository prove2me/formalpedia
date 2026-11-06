-- Prove2me | Theorems.Thm_FreeCode_foldl_lit
-- name    : FreeCode.foldl_lit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:55.901817+00:00
-- url     : https://prove2.me/theorems/2fd72461-7d94-4e36-8668-0063c01cffdb
-- title:
--   Free Code: foldl lit
-- statement:
--   In a clause: the mark 1 and the w bits of a literal put the word of the literal (last bit first)
--   on the clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L91-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L91-L95

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Mathlib.Tactic
import Definitions.Def_FreeCode_Reader
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
section
open FreeCode
open Groundwork Groundwork.Prog Groundwork.Decode
open Sat3 (Lit CNF slot)

theorem FreeCode.foldl_lit (w : ℕ) (cl : List (List Bool)) (acc : List (List (List Bool))) (bs : List Bool) (hw : bs.length = w) (h0 : bs ≠ []) :
    (true :: bs).foldl (stepR w) (false, true, [], cl, acc) = (false, true, [], bs.reverse :: cl, acc) := by sorry
