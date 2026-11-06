-- Prove2me | Theorems.Thm_GraphProblems_DomTree_sat_cons
-- name    : GraphProblems.DomTree.sat_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:02:30.349812+00:00
-- url     : https://prove2.me/theorems/ac5f8d6c-da20-4bd2-977f-6ef166e2fed4
-- title:
--   Dom Tree: sat cons
-- statement:
--   The Dom Tree construction uses the sat cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L44-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.sat_cons {C : List (ℕ × Bool)} {ψ : Fml} : Sat a (C :: ψ) ↔ (∃ l ∈ C, ext a l.1 = l.2) ∧ Sat a ψ := by sorry
