-- Prove2me | Theorems.Thm_Groundwork_Grid_ZG_congr
-- name    : Groundwork.Grid.ZG_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:41.989041+00:00
-- url     : https://prove2.me/theorems/16270f54-746a-4694-8074-8bac20597c87
-- title:
--   Grid: ZG congr
-- statement:
--   ZG reads the functions G at the rectangles only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L172-L176
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L172-L176

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_GridDefs
import Definitions.Def_StepMachines_Prog_Chunks
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_StepMachines_Math_Digits
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset
open Groundwork.Prog (digit nRect)

theorem Groundwork.Grid.ZG_congr {ρ γ α : Type} [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
    (R : Inst (ρ × γ) α) {G G' : Rect ρ γ → α → α → α → α → ℤ} (h : ∀ ω ∈ Ω ρ γ, G ω = G' ω) : ZG R G = ZG R G' := by sorry
