-- Prove2me | Theorems.Thm_Groundwork_Grid_ZG_tr
-- name    : Groundwork.Grid.ZG_tr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:32.846641+00:00
-- url     : https://prove2.me/theorems/49caf8dc-f9af-422c-aff8-70c63b3c92d3
-- title:
--   Grid: ZG tr
-- statement:
--   Transposing the grid does not change the sum.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Expand.lean#L36-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Grid/Expand.lean#L36-L46

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_RowNet
import Definitions.Def_Groundwork_Cross_Bit
import Definitions.Def_Groundwork_Grid_Expand
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
variable {ρ γ α : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ]

theorem Groundwork.Grid.ZG_tr [Fintype α] [DecidableEq α] (R : Inst (ρ × γ) α) (G : Rect ρ γ → α → α → α → α → ℤ) :
    ZG (trInst R) (trG G) = ZG R G := by sorry
