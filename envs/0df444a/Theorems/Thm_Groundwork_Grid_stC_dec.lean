-- Prove2me | Theorems.Thm_Groundwork_Grid_stC_dec
-- name    : Groundwork.Grid.stC_dec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:37:35.389419+00:00
-- url     : https://prove2.me/theorems/2e689fde-7685-43a9-a324-a64ced184a13
-- title:
--   Grid: st C dec
-- statement:
--   The state named by a word, read half-edge by half-edge.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L84-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/SideCodes.lean#L84-L87

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

theorem Groundwork.Grid.stC_dec (g : ℕ) (tr : Bool) (n : ℕ) (z : List Bool) (x : Fin g) (w' : Fin g × Fin g) :
    (stC g tr n).dec z x w' = bitsOf n (he g n z x (node g tr w'.1 w'.2)) := by sorry
