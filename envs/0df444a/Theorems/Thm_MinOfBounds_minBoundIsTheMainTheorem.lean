-- Prove2me | Theorems.Thm_MinOfBounds_minBoundIsTheMainTheorem
-- name    : MinOfBounds.minBoundIsTheMainTheorem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:59:20.394101+00:00
-- url     : https://prove2.me/theorems/aaa44377-5133-4dbf-9c21-4b1b2842deb2
-- title:
--   Min Of Bounds: min Bound Is The Main Theorem
-- statement:
--   «This is the Main Theorem.» The two bounds are the same number, because the minimum of the two
--   powers of 2 is 2 to the minimum of the two exponents.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L142-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L142-L144

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

theorem MinOfBounds.minBoundIsTheMainTheorem : MinBoundIsTheMainTheorem := by sorry
