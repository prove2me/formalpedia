-- Prove2me | Theorems.Thm_GraphProblems_Sets_mem_trueSet
-- name    : GraphProblems.Sets.mem_trueSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:34:07.737136+00:00
-- url     : https://prove2.me/theorems/ccc9a870-c232-4b72-ab39-3815c7d9b418
-- title:
--   Sets: mem true Set
-- statement:
--   A variable is in the set if and only if it is true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L36-L36
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L36-L36

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

theorem GraphProblems.Sets.mem_trueSet {a : Fin n → Bool} {i : Fin n} : i ∈ trueSet a ↔ a i = true := by sorry
