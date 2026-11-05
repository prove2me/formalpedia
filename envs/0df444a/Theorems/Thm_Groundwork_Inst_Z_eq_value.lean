-- Prove2me | Theorems.Thm_Groundwork_Inst_Z_eq_value
-- name    : Groundwork.Inst.Z_eq_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:51.052434+00:00
-- url     : https://prove2.me/theorems/0380be74-3e2c-442b-8df4-aac6dcca5d76
-- title:
--   Inst: Z eq value
-- statement:
--   An instance has the value of its network.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L167-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L167-L178

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}

theorem Groundwork.Inst.Z_eq_value [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] (R : Inst J A) (d : A) :
    R.Z d = (R.net d).value := by sorry
