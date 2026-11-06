-- Prove2me | Theorems.Thm_MinOfBounds_everyAlternationMeetsMinBound
-- name    : MinOfBounds.everyAlternationMeetsMinBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:58:34.877244+00:00
-- url     : https://prove2.me/theorems/0c42e45a-befa-4218-a52d-7f51f607c3e2
-- title:
--   Min Of Bounds: every Alternation Meets Min Bound
-- statement:
--   **The main statement.** Every machine that runs M₁ and M₂ in alternation behind a function that
--   renames the variables that occur meets the bound of Corollary 11.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L99-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L99-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_TwoMachines_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Rename_Compact
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_MinOfBounds_Main
set_option autoImplicit false
section
section
open MinOfBounds
open Turing Groundwork Wrap TwoMachines MainTheoremForms
open Sat3 (CNF)

theorem MinOfBounds.everyAlternationMeetsMinBound : EveryAlternationMeetsMinBound := by sorry
