-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_lAt_polyT
-- name    : Groundwork.Prog.NetE.lAt_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:48:56.562192+00:00
-- url     : https://prove2.me/theorems/79498a06-eaa7-42c1-8581-cf048b41d041
-- title:
--   Net E: l At poly T
-- statement:
--   The Net E construction uses the l At poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L146-L149
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L146-L149

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

theorem Groundwork.Prog.NetE.lAt_polyT {c : α → C} {x G G' : α → ℕ} {θ : α → List Bool} {p : α → ℕ × ℕ} (hc : PolyT c)
    (hx : PolyT x) (hG : PolyT G) (hG' : PolyT G') (hθ : PolyT θ) (hp : PolyT p) :
    PolyT fun t => lAt K g Np (c t) (x t) (G t) (G' t) (θ t) (p t) := by sorry
