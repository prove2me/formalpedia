-- Prove2me | Theorems.Thm_MinOfBounds_boundInMSuffices
-- name    : MinOfBounds.boundInMSuffices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:10:14.825136+00:00
-- url     : https://prove2.me/theorems/65b0e2c2-0a4f-4356-bec8-1bd87ba04b1d
-- title:
--   Min Of Bounds: bound In MSuffices
-- statement:
--   Every machine with the body of `AppRunningTime.BoundInM` and the constant C meets the bound in m
--   with the constant 3C: the factor C in front goes into the exponent (`bound_le_timeM`), and the
--   polynomial that is added only makes the bound larger.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L59-L60

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

theorem MinOfBounds.boundInMSuffices : BoundInMSuffices := by sorry
