-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_n_polyT
-- name    : Groundwork.Prog.NetE.n_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:48:50.134908+00:00
-- url     : https://prove2.me/theorems/338d932f-93e1-4596-81a2-118dae2794de
-- title:
--   Net E: n poly T
-- statement:
--   The lengths of the states, in binary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L104-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L104-L105

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

theorem Groundwork.Prog.NetE.n_polyT {c : α → C} {a : α → ℕ} (hc : PolyT c) (ha : PolyT a) : PolyT fun t => Np.n (c t) (a t) := by sorry
