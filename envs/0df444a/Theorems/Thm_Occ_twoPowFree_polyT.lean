-- Prove2me | Theorems.Thm_Occ_twoPowFree_polyT
-- name    : Occ.twoPowFree_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:09:49.764501+00:00
-- url     : https://prove2.me/theorems/91f74121-49a3-4dea-84b4-a17d59f8c782
-- title:
--   Occ: two Pow Free poly T
-- statement:
--   2^(n−v) is computed from ((n in unary, Φ), Z) in polynomial time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean#L141-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/Occ/Main.lean#L141-L142

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

theorem Occ.twoPowFree_polyT : PolyT fun q : (List Unit × Fml) × ℤ => 2 ^ (q.1.1.length - numOcc q.1.2) := by sorry
