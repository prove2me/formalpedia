-- Prove2me | Theorems.Thm_FreeCode_decidesFree_mono
-- name    : FreeCode.decidesFree_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:59.227195+00:00
-- url     : https://prove2.me/theorems/005d8211-78b1-4a91-a6f1-2e8233ff3a0d
-- title:
--   Free Code: decides Free mono
-- statement:
--   `DecidesFree Ms w δ c` stays true when δ and c are made larger.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L44-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Behind.lean#L44-L52

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Behind
set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat

theorem FreeCode.decidesFree_mono {Ms : StepMachine (List Bool) Bool} {w : ℕ} {δ δ' : ℝ} {c c' : ℕ} (hδ : δ ≤ δ') (hc : c ≤ c') (h : DecidesFree Ms w δ c) :
    DecidesFree Ms w δ' c' := by sorry
