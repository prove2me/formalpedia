-- Prove2me | Theorems.Thm_FromPrinted_Consequences_stDominatingCounted
-- name    : FromPrinted.Consequences.stDominatingCounted
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:32:14.192441+00:00
-- url     : https://prove2.me/theorems/4a2ec5e6-b716-4908-94ff-8aac7a2204e6
-- title:
--   Consequences: st Dominating Counted
-- statement:
--   **Dominating sets of size s, with the machine named.** For every δ > 0 there are w, ℓ, τ, c such
--   that the tree that shortens the clauses to w literals has at most 2^{(δ/2)n} leaves
--   (`ShortensD w (δ/2)`), and `DOMcount w ℓ τ` has polynomial-time steps and returns, on the code of
--   (G, s), s ≤ n, the number of dominating sets of size s within c·2^{δn} steps, on states of size at
--   most c·(n+2)^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Dom.lean#L41-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Dom.lean#L41-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Sets
import Definitions.Def_Consequences_Dom
import Definitions.Def_SplitCount_Sizes
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_DomTree
import Definitions.Def_CountKSat_Walk
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Dom
set_option autoImplicit false
section
section
open Consequences SplitCount
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog Groundwork.Stepped Groundwork.Sparsify CountKSat GraphProblems Paper

theorem FromPrinted.Consequences.stDominatingCounted : StDominatingCounted := by sorry
