-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_isW_polyT
-- name    : Groundwork.Prog.NetE.isW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:59:12.146674+00:00
-- url     : https://prove2.me/theorems/4ce18685-6cdc-4559-ab54-c492f4df5f10
-- title:
--   Net E: is W poly T
-- statement:
--   The Net E construction uses the is W poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L184-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L184-L184

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
variable {α β : Type} [Enc α] [Enc β]
variable (K g : ℕ)
variable {C : Type} [Enc C] {Np : PNet C}

theorem Groundwork.Prog.NetE.isW_polyT : PolyT (isW g : (X0 C × ℕ) × ℕ → Bool) := by sorry
