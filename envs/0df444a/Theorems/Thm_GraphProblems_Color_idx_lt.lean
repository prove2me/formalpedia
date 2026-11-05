-- Prove2me | Theorems.Thm_GraphProblems_Color_idx_lt
-- name    : GraphProblems.Color.idx_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:53.097569+00:00
-- url     : https://prove2.me/theorems/5919fc14-1251-4ba7-b46c-070e86a8a4ab
-- title:
--   Color: idx lt
-- statement:
--   The Color construction uses the idx lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L31-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L31-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Color
open Blocks

theorem GraphProblems.Color.idx_lt {n k v c : ℕ} (hv : v < n) (hc : c < k) : v * k + c < n * k := by sorry
