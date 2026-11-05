-- Prove2me | Theorems.Thm_Occ_stSameAsFin
-- name    : Occ.stSameAsFin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:38:18.972116+00:00
-- url     : https://prove2.me/theorems/6e1d27aa-7c10-4101-81a1-b880d261b96a
-- title:
--   Occ: st Same As Fin
-- statement:
--   For a formula φ with variables in `Fin N`, the number of variables that occur in `Decode.toN φ`
--   is `MainTheoremForms.numOcc φ`, and the number of assignments of these variables that satisfy
--   `Decode.toN φ` is `MainTheoremForms.numSatOcc φ`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean#L88-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean#L88-L102

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

theorem Occ.stSameAsFin : StSameAsFin := by sorry
