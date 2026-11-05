-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_Pc_le_Uc
-- name    : Groundwork.Prog.NetE.Pc_le_Uc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:13:52.409299+00:00
-- url     : https://prove2.me/theorems/7a015cc7-2b4d-492e-88c7-b80c1ca8f4bc
-- title:
--   Net E: Pc le Uc
-- statement:
--   The Net E construction uses the Pc le Uc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L166-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L166-L171

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
omit h [Enc C]

theorem Groundwork.Prog.NetE.Pc_le_Uc (Np : PNet C) (c : C) : Pc g Np c ≤ Uc g Np c := by sorry
