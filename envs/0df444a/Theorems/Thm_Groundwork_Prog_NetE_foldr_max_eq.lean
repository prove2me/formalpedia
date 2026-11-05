-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_foldr_max_eq
-- name    : Groundwork.Prog.NetE.foldr_max_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:14:08.934669+00:00
-- url     : https://prove2.me/theorems/8899119f-8cf1-4efc-b3df-1b51793bcefc
-- title:
--   Net E: foldr max eq
-- statement:
--   The Net E construction uses the foldr max eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L46-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L46-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_ToTuring_Poly_NetFun
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE

theorem Groundwork.Prog.NetE.foldr_max_eq (l : List ℕ) : l.foldr max 0 = (l.find? fun m => l.all fun k => decide (k ≤ m)).getD 0 := by sorry
