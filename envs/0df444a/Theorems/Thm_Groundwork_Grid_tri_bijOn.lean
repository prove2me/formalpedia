-- Prove2me | Theorems.Thm_Groundwork_Grid_tri_bijOn
-- name    : Groundwork.Grid.tri_bijOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:38:39.223328+00:00
-- url     : https://prove2.me/theorems/d96307e9-1fe4-4a6d-9c98-7d9b3aae4163
-- title:
--   Grid: tri bij On
-- statement:
--   The pairs i < i' below g are numbered 0, …, c2 g − 1 by tri, each number once.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L100-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/Digits.lean#L100-L113

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

theorem Groundwork.Grid.tri_bijOn (g : ℕ) : Set.BijOn (fun k : Fin g × Fin g => tri k.1 k.2) {k | k.1 < k.2} (range (c2 g)) := by sorry
