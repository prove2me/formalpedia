-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_value_congr
-- name    : Groundwork.Prog.Count.value_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:22:31.677777+00:00
-- url     : https://prove2.me/theorems/1490cde9-ebc9-4f18-8d56-f80b7ffa2d0f
-- title:
--   Count: value congr
-- statement:
--   Two networks that agree along a bijection of their states have the same value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L377-L396
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L377-L396

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

theorem Groundwork.Prog.Count.value_congr {J σ τ σ' τ' : Type} [Fintype J] [LinearOrder J] (N : Network J σ τ) (N' : Network J σ' τ')
    (es : σ' → σ) (hS : ∀ a, Set.BijOn es (N'.S a) (N.S a)) (hW : ∀ a z, N'.W a z = N.W a (es z))
    (hΨ : ∀ a b, a < b → ∀ z z', N'.Ψ a b z z' = N.Ψ a b (es z) (es z')) : N'.value = N.value := by sorry
