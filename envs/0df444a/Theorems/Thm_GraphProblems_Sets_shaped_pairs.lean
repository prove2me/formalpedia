-- Prove2me | Theorems.Thm_GraphProblems_Sets_shaped_pairs
-- name    : GraphProblems.Sets.shaped_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:41:37.400639+00:00
-- url     : https://prove2.me/theorems/91a65eef-f771-4dc4-8721-49456a448699
-- title:
--   Sets: shaped pairs
-- statement:
--   Width, variables and number of clauses of such a formula.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L82-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L82-L95

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

theorem GraphProblems.Sets.shaped_pairs (n : ℕ) (q : ℕ × ℕ → Bool) (b : Bool) :
    Shaped 2 n (((pairs n).filter q).map fun p => [(p.1, b), (p.2, b)]) ∧ (((pairs n).filter q).map fun p => [(p.1, b), (p.2, b)]).length ≤ n * n := by sorry
