-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_stLen_unary
-- name    : Groundwork.Prog.NetE.stLen_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:57:52.051338+00:00
-- url     : https://prove2.me/theorems/a4f91773-b741-455e-96f1-5a52abd7503b
-- title:
--   Net E: st Len unary
-- statement:
--   The Net E construction uses the st Len unary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L116-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L116-L118

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
variable (h : Np.Keeps)
include h

theorem Groundwork.Prog.NetE.stLen_unary : Unary (fun p : C × ℕ × ℕ => stLen K g Np p.1 p.2.1 p.2.2) := by sorry
