-- Prove2me | Theorems.Thm_Groundwork_Code_full_blocks
-- name    : Groundwork.Code.full_blocks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:34:04.613672+00:00
-- url     : https://prove2.me/theorems/29748d3c-c618-4f0b-bd97-628222e4cc28
-- title:
--   Code: full blocks
-- statement:
--   The Code construction uses the full blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L111-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/CodeMore.lean#L111-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Math_Code
import Mathlib.Data.List.GetD
import Definitions.Def_StepMachines_Math_CodeMore
set_option autoImplicit false
section
open Groundwork
open Finset
variable {X Y : Type*}
open Groundwork.Code
variable {S : Finset X} {n : ℕ}

theorem Groundwork.Code.full_blocks {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} (pos : ι ≃ Fin r) {m : ℕ} (c : Code S m)
    (h : c.Full) : (blocks pos c).Full := by sorry
