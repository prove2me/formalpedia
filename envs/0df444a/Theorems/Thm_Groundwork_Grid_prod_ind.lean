-- Prove2me | Theorems.Thm_Groundwork_Grid_prod_ind
-- name    : Groundwork.Grid.prod_ind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:56:50.873567+00:00
-- url     : https://prove2.me/theorems/295b0d29-0e55-40a2-a479-e5d50db5ab69
-- title:
--   Grid: prod ind
-- statement:
--   A product of indicators is the indicator of «all of them hold».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L41-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Grid.lean#L41-L44

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

theorem Groundwork.Grid.prod_ind {ι : Type} (s : Finset ι) (p : ι → Prop) [DecidablePred p] {P : Prop} [Decidable P]
    (h : P ↔ ∀ i ∈ s, p i) : ∏ i ∈ s, (if p i then (1 : ℤ) else 0) = if P then 1 else 0 := by sorry
