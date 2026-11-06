-- Prove2me | Theorems.Thm_MinOfBounds_theTwoTheoremsImplyMinBound
-- name    : MinOfBounds.theTwoTheoremsImplyMinBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:55:17.457295+00:00
-- url     : https://prove2.me/theorems/de3c4c27-10ba-4ed4-a2bd-10c8128174e4
-- title:
--   Min Of Bounds: the Two Theorems Imply Min Bound
-- statement:
--   The bound in m and Theorem D (b) imply Corollary 11 on the compact code: take a machine for each
--   of the two, a machine that runs them in alternation behind the renaming, and the constant that the
--   main statement gives for it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L131-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L131-L138

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

theorem MinOfBounds.theTwoTheoremsImplyMinBound : TheTwoTheoremsImplyMinBound := by sorry
