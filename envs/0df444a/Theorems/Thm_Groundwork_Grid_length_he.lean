-- Prove2me | Theorems.Thm_Groundwork_Grid_length_he
-- name    : Groundwork.Grid.length_he
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:42:54.385237+00:00
-- url     : https://prove2.me/theorems/31e44abd-7960-427d-866d-d9d12e5cb4aa
-- title:
--   Grid: length he
-- statement:
--   A half-edge in the word of a state has ℓ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L55-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L55-L60

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_CutWord
import Definitions.Def_StepMachines_Math_Digits
import Definitions.Def_StepMachines_Prog_Brute
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Math_SideCodes
set_option autoImplicit false
section
section
open Groundwork Groundwork.Grid
open Finset

theorem Groundwork.Grid.length_he {g ℓ : ℕ} {z : List Bool} (hz : z.length = g ^ 3 * ℓ) {x u : ℕ} (hx : x < g) (hu : u < g * g) :
    (he g ℓ z x u).length = ℓ := by sorry
