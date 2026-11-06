-- Prove2me | Theorems.Thm_MinOfBounds_everyAlternationDecidesWithinMinBound
-- name    : MinOfBounds.everyAlternationDecidesWithinMinBound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:58:49.924506+00:00
-- url     : https://prove2.me/theorems/f5dd5d25-5f19-43a7-808a-eaf5a73fcb4f
-- title:
--   Min Of Bounds: every Alternation Decides Within Min Bound
-- statement:
--   The same for deciding: “some bit is 1” of the number of satisfying assignments in n + 1 bits is
--   the bit “this number is not 0”, and φ is satisfiable if and only if this number is not 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L103-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Main.lean#L103-L110

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

theorem MinOfBounds.everyAlternationDecidesWithinMinBound : EveryAlternationDecidesWithinMinBound := by sorry
