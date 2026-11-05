-- Prove2me | Theorems.Thm_GraphProblems_DomTree_sat_map_posC
-- name    : GraphProblems.DomTree.sat_map_posC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:12:43.840874+00:00
-- url     : https://prove2.me/theorems/d521f4a0-7119-465e-81f2-db2306259741
-- title:
--   Dom Tree: sat map pos C
-- statement:
--   The Dom Tree construction uses the sat map pos C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L49-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L49-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.sat_map_posC {O : List (List ℕ)} : Sat a (O.map posC) ↔ ∀ D ∈ O, Hit a D := by sorry
