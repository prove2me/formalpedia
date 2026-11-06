-- Prove2me | Theorems.Thm_GraphProblems_DomTree_sat_units
-- name    : GraphProblems.DomTree.sat_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:02:05.144931+00:00
-- url     : https://prove2.me/theorems/249246c3-817c-47e8-9780-1837812d21c4
-- title:
--   Dom Tree: sat units
-- statement:
--   The Dom Tree construction uses the sat units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L52-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L52-L53

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

theorem GraphProblems.DomTree.sat_units {H : List ℕ} : Sat a (H.map fun u => [(u, false)]) ↔ ¬Hit a H := by sorry
