-- Prove2me | Theorems.Thm_GraphProblems_Sets_sat_indepF
-- name    : GraphProblems.Sets.sat_indepF
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:41:20.865087+00:00
-- url     : https://prove2.me/theorems/b9d2fb64-579e-4144-b39c-323dcbca6973
-- title:
--   Sets: sat indep F
-- statement:
--   An assignment satisfies the formula of Independent Set if and only if its set is independent.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L100-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L100-L111

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
variable (G : SimpleGraph (Fin n)) (a : Fin n → Bool)

theorem GraphProblems.Sets.sat_indepF : (∀ C ∈ indepF n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ G.IsIndepSet (trueSet a : Set (Fin n)) := by sorry
