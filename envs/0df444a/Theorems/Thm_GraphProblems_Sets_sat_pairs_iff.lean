-- Prove2me | Theorems.Thm_GraphProblems_Sets_sat_pairs_iff
-- name    : GraphProblems.Sets.sat_pairs_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:41:14.74256+00:00
-- url     : https://prove2.me/theorems/14422a83-097c-4654-929a-d800cbdb2f3e
-- title:
--   Sets: sat pairs iff
-- statement:
--   An assignment satisfies the formula with one clause of two literals of the same sign b for every
--   pair chosen by q if and only if, for every such pair, one of its two variables has the value b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L71-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L71-L79

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

theorem GraphProblems.Sets.sat_pairs_iff (q : ℕ × ℕ → Bool) (b : Bool) (a : Fin n → Bool) :
    (∀ C ∈ ((pairs n).filter q).map fun p => [(p.1, b), (p.2, b)], ∃ l ∈ C, CountKSat.ext a l.1 = l.2)
      ↔ ∀ u v : Fin n, q (u.val, v.val) = true → a u = b ∨ a v = b := by sorry
