-- Prove2me | Theorems.Thm_GraphProblems_Sets_mem_pairs
-- name    : GraphProblems.Sets.mem_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:34:38.284872+00:00
-- url     : https://prove2.me/theorems/5a049902-009b-4220-b8f0-5a44d836f6f3
-- title:
--   Sets: mem pairs
-- statement:
--   The pairs are those of two numbers below n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L65-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L65-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open GraphProblems.Sets
variable {n : ℕ}

theorem GraphProblems.Sets.mem_pairs {n : ℕ} {p : ℕ × ℕ} : p ∈ pairs n ↔ p.1 < n ∧ p.2 < n := by sorry
