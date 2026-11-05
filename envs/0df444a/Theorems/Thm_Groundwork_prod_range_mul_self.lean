-- Prove2me | Theorems.Thm_Groundwork_prod_range_mul_self
-- name    : Groundwork.prod_range_mul_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:50.954194+00:00
-- url     : https://prove2.me/theorems/190d1514-ff58-463c-a765-af7daa1fd3a4
-- title:
--   Groundwork: prod range mul self
-- statement:
--   A product over i < g*g as a product over pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L91-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L91-L96

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset

theorem Groundwork.prod_range_mul_self (g : ℕ) (F : ℕ → ℤ) :
    ∏ i ∈ range (g * g), F i = ∏ p : Fin g × Fin g, F (p.1.val * g + p.2.val) := by sorry
