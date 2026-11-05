-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_zOf_polyT
-- name    : Groundwork.Prog.NetE.zOf_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:48:42.453993+00:00
-- url     : https://prove2.me/theorems/7645c8fb-7c71-4b48-bc4d-338ea236dcf1
-- title:
--   Net E: z Of poly T
-- statement:
--   The Net E construction uses the z Of poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L127-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L127-L129

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

theorem Groundwork.Prog.NetE.zOf_polyT : PolyT (zOf K g Np) := by sorry
