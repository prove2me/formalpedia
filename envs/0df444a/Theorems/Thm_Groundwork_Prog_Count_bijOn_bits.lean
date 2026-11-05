-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_bijOn_bits
-- name    : Groundwork.Prog.Count.bijOn_bits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:11.982745+00:00
-- url     : https://prove2.me/theorems/ab5b2812-d9dd-4361-b12a-45ce18a30a61
-- title:
--   Count: bij On bits
-- statement:
--   The Count construction uses the bij On bits property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L194-L211
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L194-L211

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}

theorem Groundwork.Prog.Count.bijOn_bits : Set.BijOn (bits (μ := μ) (k := k)) (words (μ * k)) (univ : Finset (Sl μ k → Bool)) := by sorry
