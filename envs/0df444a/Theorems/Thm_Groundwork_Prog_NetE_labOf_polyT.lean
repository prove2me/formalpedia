-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_labOf_polyT
-- name    : Groundwork.Prog.NetE.labOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:49:12.46463+00:00
-- url     : https://prove2.me/theorems/10d3649d-d313-48e4-acc3-84bf4019879c
-- title:
--   Net E: lab Of poly T
-- statement:
--   The Net E construction uses the lab Of poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L176-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L176-L178

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

theorem Groundwork.Prog.NetE.labOf_polyT {u : α → X0 C} {a b : α → ℕ} (hu : PolyT u) (ha : PolyT a) (hb : PolyT b) :
    PolyT fun t => labOf K g Np (u t) (a t) (b t) := by sorry
