-- Prove2me | Theorems.Thm_GraphProblems_DomTree_inv_step
-- name    : GraphProblems.DomTree.inv_step
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:03:08.822535+00:00
-- url     : https://prove2.me/theorems/7a9b76c7-32cd-4552-929e-566cad44141e
-- title:
--   Dom Tree: inv step
-- statement:
--   The Dom Tree construction uses the inv step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L160-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/GraphProblems/DomTree.lean#L160-L197

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

theorem GraphProblems.DomTree.inv_step {n s w : ℕ} (hw : 1 ≤ w) (x : DNode) (p t : ℕ) (l h : DNode) (hG : Inv n s w x p t) (e : stepD w x = some (l, h)) :
    Inv n s w l (p + 1) t ∧ Inv n s w h (p + 1) (t + w) := by sorry
