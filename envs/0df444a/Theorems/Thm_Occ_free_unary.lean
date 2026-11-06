-- Prove2me | Theorems.Thm_Occ_free_unary
-- name    : Occ.free_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:58.665367+00:00
-- url     : https://prove2.me/theorems/c6567838-cedf-4b92-80a2-711bb149db48
-- title:
--   Occ: free unary
-- statement:
--   n − v in unary is computed from ((n in unary, Φ), Z) in polynomial time: it is at most n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean#L136-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean#L136-L138

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Occ
open Groundwork Groundwork.Prog CountKSat

theorem Occ.free_unary : Unary fun q : (List Unit × Fml) × ℤ => q.1.1.length - numOcc q.1.2 := by sorry
