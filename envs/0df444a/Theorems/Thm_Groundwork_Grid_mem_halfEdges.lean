-- Prove2me | Theorems.Thm_Groundwork_Grid_mem_halfEdges
-- name    : Groundwork.Grid.mem_halfEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:17:08.616277+00:00
-- url     : https://prove2.me/theorems/8be4a212-a009-4708-8dac-03f498146bd1
-- title:
--   Grid: mem half Edges
-- statement:
--   The half-edge labellings of Inst.Z_eq_halfEdges are those with the default label at every node
--   itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L115-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L115-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Defs
import Definitions.Def_Groundwork_Net_Net
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Groundwork_Grid_Grid
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {J ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [DecidableEq α]

theorem Groundwork.Grid.mem_halfEdges [Fintype J] [DecidableEq J] (d : α) (ℓ : J → J → α) :
    ℓ ∈ (Fintype.piFinset fun w : J => tuples (fun w' => w' ≠ w) (fun _ => (univ : Finset α)) d) ↔
      ∀ w, ℓ w w = d := by sorry
