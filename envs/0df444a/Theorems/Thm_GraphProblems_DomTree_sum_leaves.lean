-- Prove2me | Theorems.Thm_GraphProblems_DomTree_sum_leaves
-- name    : GraphProblems.DomTree.sum_leaves
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:03:10.557183+00:00
-- url     : https://prove2.me/theorems/03bd0a23-cc5f-4538-b233-38f9ddce4f86
-- title:
--   Dom Tree: sum leaves
-- statement:
--   A number that is the sum of the numbers of the two children is the sum of the numbers of the
--   leaves.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L127-L136
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L127-L136

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Interfaces
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_GraphProblems_DomTree
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
open GraphProblems GraphProblems.DomTree
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat Finset
variable {n : ℕ} {a : Fin n → Bool}

theorem GraphProblems.DomTree.sum_leaves {σ : Type} (step : σ → Option (σ × σ)) (f : σ → ℕ) (hf : ∀ s l h, step s = some (l, h) → f s = f l + f h)
    (k : ℕ) (s : σ) : f s = ((leaves step k s).map f).sum := by sorry
