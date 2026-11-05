-- Prove2me | Theorems.Thm_Groundwork_Stepped_mapOut_reaches
-- name    : Groundwork.Stepped.mapOut_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:40:57.206293+00:00
-- url     : https://prove2.me/theorems/3af2071c-093c-4774-bfd6-3b2bb56bc280
-- title:
--   Stepped: map Out reaches
-- statement:
--   The Stepped construction uses the map Out reaches property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L147-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/Stepped.lean#L147-L151

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

theorem Groundwork.Stepped.mapOut_reaches {M : Stepped α β} {f : β → γ} {s : M.σ} {t S : ℕ} {b : β} (h : M.Reaches S b s t) :
    (mapOut M f).Reaches S (f b) s t := by sorry
