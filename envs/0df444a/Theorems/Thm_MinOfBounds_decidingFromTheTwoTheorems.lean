-- Prove2me | Theorems.Thm_MinOfBounds_decidingFromTheTwoTheorems
-- name    : MinOfBounds.decidingFromTheTwoTheorems
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:56:13.205512+00:00
-- url     : https://prove2.me/theorems/7cf543e1-60dc-440e-87e2-d904acfa48b2
-- title:
--   Min Of Bounds: deciding From The Two Theorems
-- statement:
--   The same for deciding; “some bit is 1” is polynomial-time (`VariableBound.Rename.anyBit_polyT`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L121-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L121-L126

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

theorem MinOfBounds.decidingFromTheTwoTheorems : DecidingFromTheTwoTheorems := by sorry
