-- Prove2me | Theorems.Thm_GraphProblems_DomTree_sat_light
-- name    : GraphProblems.DomTree.sat_light
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:02:31.652489+00:00
-- url     : https://prove2.me/theorems/19bf0558-33f6-429f-ac05-0ff7619cea19
-- title:
--   Dom Tree: sat light
-- statement:
--   The light child: the node, and a variable of H is true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L56-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L56-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_Groundwork_PolyT_filter
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.filter
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.sat_light {O : List (List ℕ)} {F : Fml} {C : List ℕ} (w : ℕ) :
    Sat a ((O.filter fun D => D != C).map posC ++ (posC (C.take w) :: F)) ↔ Sat a (O.map posC ++ F) ∧ Hit a (C.take w) := by sorry
