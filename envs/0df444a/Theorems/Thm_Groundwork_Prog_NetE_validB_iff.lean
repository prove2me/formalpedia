-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_validB_iff
-- name    : Groundwork.Prog.NetE.validB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:07.279818+00:00
-- url     : https://prove2.me/theorems/67fa6b5a-1e2c-448f-aba0-c017e1f3fd8a
-- title:
--   Net E: valid B iff
-- statement:
--   The Net E construction uses the valid B iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L334-L354
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L334-L354

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)

theorem Groundwork.Prog.NetE.validB_iff (c : C) (x β : ℕ) (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) :
    validB K g Np ((c, x), (G.val, List.ofFn θ)) = true ↔
      ∀ G' : Fin K, G' ≠ G → θ G' ∈ mD K g Np c x β (min G G') (max G G') := by sorry
