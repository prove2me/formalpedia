-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_foldr_max_mem
-- name    : Groundwork.Prog.NetE.foldr_max_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:13:22.552532+00:00
-- url     : https://prove2.me/theorems/8c3ec228-892a-4612-b5c8-b98b9bfa72fd
-- title:
--   Net E: foldr max mem
-- statement:
--   The Net E construction uses the foldr max mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L35-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L35-L44

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_ToTuring_Poly_NetFun
set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE

theorem Groundwork.Prog.NetE.foldr_max_mem {l : List ℕ} (h : l ≠ []) : l.foldr max 0 ∈ l := by sorry
