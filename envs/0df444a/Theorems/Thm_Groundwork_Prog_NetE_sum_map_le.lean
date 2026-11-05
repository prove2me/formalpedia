-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_sum_map_le
-- name    : Groundwork.Prog.NetE.sum_map_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:13.20717+00:00
-- url     : https://prove2.me/theorems/bbea0574-e9c1-4886-8b5b-ce138eaf6398
-- title:
--   Net E: sum map le
-- statement:
--   The Net E construction uses the sum map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L27-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L27-L35

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)

theorem Groundwork.Prog.NetE.sum_map_le {ι : Type} (l : List ι) (f : ι → ℕ) (M : ℕ) (h : ∀ i ∈ l, f i ≤ M) :
    (l.map f).sum ≤ l.length * M := by sorry
