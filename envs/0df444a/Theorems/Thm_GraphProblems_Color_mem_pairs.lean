-- Prove2me | Theorems.Thm_GraphProblems_Color_mem_pairs
-- name    : GraphProblems.Color.mem_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:36:14.923832+00:00
-- url     : https://prove2.me/theorems/819f10ac-9110-431b-a4be-0241b8d7623b
-- title:
--   Color: mem pairs
-- statement:
--   The Color construction uses the mem pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L28-L29
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Color.lean#L28-L29

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

theorem GraphProblems.Color.mem_pairs {n : ℕ} {p : ℕ × ℕ} : p ∈ pairs n ↔ p.1 < n ∧ p.2 < n := by sorry
