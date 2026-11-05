-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_cap_polyT
-- name    : Groundwork.Prog.NetE.cap_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:48:53.026722+00:00
-- url     : https://prove2.me/theorems/1e937564-e275-498f-a950-4c7d00b8d023
-- title:
--   Net E: cap poly T
-- statement:
--   The lengths of the labels, in binary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L108-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L108-L110

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

theorem Groundwork.Prog.NetE.cap_polyT {c : α → C} {a b : α → ℕ} (hc : PolyT c) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun t => Np.cap (c t) (a t) (b t) := by sorry
