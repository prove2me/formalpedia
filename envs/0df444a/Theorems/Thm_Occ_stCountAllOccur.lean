-- Prove2me | Theorems.Thm_Occ_stCountAllOccur
-- name    : Occ.stCountAllOccur
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:08:54.874214+00:00
-- url     : https://prove2.me/theorems/3b2b338b-297f-4e37-ac7c-5a922db91fd4
-- title:
--   Occ: st Count All Occur
-- statement:
--   If every one of x₀ … xₙ₋₁ occurs in Φ and no other variable does, the number of satisfying
--   assignments on x₀ … xₙ₋₁ is `Eight.numSat Φ`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean#L117-L122
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean#L117-L122

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Occ_Defs
import Definitions.Def_GraphProblems_Engine
import Definitions.Def_CountKSat_InOut
import Definitions.Def_VariableBound_Paper_Rename_Math
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Int
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.Pi
import Definitions.Def_Occ_Main
set_option autoImplicit false
section
section
open Occ
open Groundwork Groundwork.Prog CountKSat

theorem Occ.stCountAllOccur : StCountAllOccur := by sorry
