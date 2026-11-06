-- Prove2me | Theorems.Thm_FreeCode_foldl_bits
-- name    : FreeCode.foldl_bits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:26:50.796829+00:00
-- url     : https://prove2.me/theorems/8661a61b-6bd8-4de0-b4f7-963611b9208d
-- title:
--   Free Code: foldl bits
-- statement:
--   Inside a literal: when the bits still to come fill the literal up to w bits, the reader ends in
--   the clause, with the word of the literal (last bit first) put on the clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L77-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L77-L87

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

theorem FreeCode.foldl_bits (w : ℕ) (cl : List (List Bool)) (acc : List (List (List Bool))) : ∀ (bs cur : List Bool), bs ≠ [] → cur.length + bs.length = w →
    bs.foldl (stepR w) (true, false, cur, cl, acc) = (false, true, [], (bs.reverse ++ cur) :: cl, acc)
  := by sorry
