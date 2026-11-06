-- Prove2me | Theorems.Thm_GraphProblems_Blocks_ext_val
-- name    : GraphProblems.Blocks.ext_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:41:43.137842+00:00
-- url     : https://prove2.me/theorems/fd55006c-42ea-46f7-92db-a4b29e695f79
-- title:
--   Blocks: ext val
-- statement:
--   The Blocks construction uses the ext val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Blocks.lean#L34-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Blocks.lean#L34-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_GraphProblems_Blocks
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Blocks

theorem GraphProblems.Blocks.ext_val {n : ℕ} (a : Fin n → Bool) (k : Fin n) : ext a k = a k := by sorry
