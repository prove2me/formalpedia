-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_le_foldr_max
-- name    : Groundwork.Prog.NetE.le_foldr_max
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:51:35.340601+00:00
-- url     : https://prove2.me/theorems/ab59a007-df30-46b7-9298-cd4e4421e6a0
-- title:
--   Net E: le foldr max
-- statement:
--   The Net E construction uses the le foldr max property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L26-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L26-L33

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

theorem Groundwork.Prog.NetE.le_foldr_max {l : List ℕ} {k : ℕ} (h : k ∈ l) : k ≤ l.foldr max 0 := by sorry
