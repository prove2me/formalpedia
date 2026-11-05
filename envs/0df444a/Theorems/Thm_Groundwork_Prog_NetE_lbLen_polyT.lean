-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_lbLen_polyT
-- name    : Groundwork.Prog.NetE.lbLen_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:48:45.675504+00:00
-- url     : https://prove2.me/theorems/3b7ce9bd-add0-432e-8185-79b0e1a975e7
-- title:
--   Net E: lb Len poly T
-- statement:
--   The Net E construction uses the lb Len poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L142-L144
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L142-L144

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

theorem Groundwork.Prog.NetE.lbLen_polyT {c : α → C} {x G G' : α → ℕ} (hc : PolyT c) (hx : PolyT x) (hG : PolyT G)
    (hG' : PolyT G') : PolyT fun t => lbLen K g Np (c t) (x t) (G t) (G' t) := by sorry
