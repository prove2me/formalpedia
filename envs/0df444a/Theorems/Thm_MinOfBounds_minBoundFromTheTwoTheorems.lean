-- Prove2me | Theorems.Thm_MinOfBounds_minBoundFromTheTwoTheorems
-- name    : MinOfBounds.minBoundFromTheTwoTheorems
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T02:10:26.237087+00:00
-- url     : https://prove2.me/theorems/ef1886a8-93c2-4c3f-b2f0-8809987c5c9c
-- title:
--   Min Of Bounds: min Bound From The Two Theorems
-- statement:
--   Existence, by `renamingFrontEndExists` and `TwoMachines.everyTwoMachinesCanBeAlternated`, and
--   the main statement.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L114-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L114-L118

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

theorem MinOfBounds.minBoundFromTheTwoTheorems : MinBoundFromTheTwoTheorems := by sorry
