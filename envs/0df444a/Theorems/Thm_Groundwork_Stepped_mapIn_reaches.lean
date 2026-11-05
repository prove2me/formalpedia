-- Prove2me | Theorems.Thm_Groundwork_Stepped_mapIn_reaches
-- name    : Groundwork.Stepped.mapIn_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:03.108199+00:00
-- url     : https://prove2.me/theorems/a0fed2d6-1dc0-4b2d-bb64-29da97cc0d30
-- title:
--   Stepped: map In reaches
-- statement:
--   The Stepped construction uses the map In reaches property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L131-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L131-L135

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachineStatements
import Definitions.Def_StepMachines_Prog_Stepped
set_option autoImplicit false
section
open Groundwork
open Groundwork.Stepped
variable {α β γ τ : Type}

theorem Groundwork.Stepped.mapIn_reaches {f : α → β} {M : Stepped β γ} {s : M.σ} {t S : ℕ} {c : γ} (h : M.Reaches S c s t) :
    (mapIn f M).Reaches S c s t := by sorry
