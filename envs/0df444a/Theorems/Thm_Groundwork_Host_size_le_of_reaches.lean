-- Prove2me | Theorems.Thm_Groundwork_Host_size_le_of_reaches
-- name    : Groundwork.Host.size_le_of_reaches
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:47:08.82426+00:00
-- url     : https://prove2.me/theorems/25357124-f5c9-43e8-a8fc-68a5bae9fc8e
-- title:
--   Host: size le of reaches
-- statement:
--   The Host construction uses the size le of reaches property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L194-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L194-L197

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
variable {M : Stepped (List Bool) Bool}

theorem Groundwork.Host.size_le_of_reaches {S t : ℕ} {b : Bool} {s : M.σ} (h : M.Reaches S b s t) : size s ≤ S := by sorry
