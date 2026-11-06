-- Prove2me | Theorems.Thm_FreeCode_foldl_lits
-- name    : FreeCode.foldl_lits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:28:11.091748+00:00
-- url     : https://prove2.me/theorems/cb044013-7d47-4b42-bcc1-806e81da477b
-- title:
--   Free Code: foldl lits
-- statement:
--   In a clause: the literals of C, each behind its mark, are put on the clause.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L98-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Reader.lean#L98-L108

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

theorem FreeCode.foldl_lits {n : ℕ} (acc : List (List (List Bool))) : ∀ (C : List (Lit n)) (cl : List (List Bool)),
    (C.flatMap fun l => true :: SatFree.encLit l).foldl (stepR (Nat.log2 (2 * n) + 1)) (false, true, [], cl, acc) =
      (false, true, [], (C.map fun l => (SatFree.encLit l).reverse).reverse ++ cl, acc)
  := by sorry
