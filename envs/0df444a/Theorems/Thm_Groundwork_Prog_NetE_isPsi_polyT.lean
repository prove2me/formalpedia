-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_isPsi_polyT
-- name    : Groundwork.Prog.NetE.isPsi_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:59:19.028014+00:00
-- url     : https://prove2.me/theorems/910b7ba0-57da-45a2-b199-420af2ce2cbe
-- title:
--   Net E: is Psi poly T
-- statement:
--   The Net E construction uses the is Psi poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L186-L186
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Poly/NetFun.lean#L186-L186

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

theorem Groundwork.Prog.NetE.isPsi_polyT : PolyT (isPsi K g : (X0 C × ℕ) × ℕ → Bool) := by sorry
