-- Prove2me | Theorems.Thm_GraphProblems_Sets_sat_domF
-- name    : GraphProblems.Sets.sat_domF
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:41:08.041701+00:00
-- url     : https://prove2.me/theorems/73a740a0-e75f-4c14-9e76-199b28a08cc4
-- title:
--   Sets: sat dom F
-- statement:
--   An assignment satisfies the formula of Dominating Set if and only if its set is dominating.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L114-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/Sets.lean#L114-L139

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

theorem GraphProblems.Sets.sat_domF : (∀ C ∈ domF n (matrix G), ∃ l ∈ C, CountKSat.ext a l.1 = l.2) ↔ IsDominating G (trueSet a) := by sorry
