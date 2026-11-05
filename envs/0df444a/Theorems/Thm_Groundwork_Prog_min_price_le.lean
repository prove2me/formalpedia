-- Prove2me | Theorems.Thm_Groundwork_Prog_min_price_le
-- name    : Groundwork.Prog.min_price_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:18.446983+00:00
-- url     : https://prove2.me/theorems/2bcae86b-ee30-4025-be89-ec62316d8d9c
-- title:
--   Prog: min price le
-- statement:
--   The cheaper total is at most the average: at most ρ·g⁴λ + g⁴/2 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L64-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridDefs.lean#L64-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NetworkStatements
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Prog_Comb
import Definitions.Def_StepMachines_Math_GridArith
import Definitions.Def_StepMachines_Prog_GridDefs
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog
open Finset Stepped

theorem Groundwork.Prog.min_price_le (g n y : ℕ) :
    ((min (priceRow g n y) (priceCol g n y) : ℕ) : ℝ) ≤ ρ * ((g : ℝ) ^ 4 * n) + (g : ℝ) ^ 4 / 2 := by sorry
