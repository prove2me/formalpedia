-- Prove2me | Theorems.Thm_Groundwork_Inst_toInst_net
-- name    : Groundwork.Inst.toInst_net
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:38.927671+00:00
-- url     : https://prove2.me/theorems/6423901e-00cd-41bf-a90d-e8da7191f2d5
-- title:
--   Inst: to Inst net
-- statement:
--   An instance, made into a network and back into an instance over a larger alphabet, is the padded
--   instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L128-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L128-L157

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

theorem Groundwork.Inst.toInst_net [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] [DecidableEq A'] (R : Inst J A) (d : A)
    (D : Finset A') (dec : A' → A) : (R.net d).toInst (fun _ _ => D) (fun _ _ => dec) = R.pad d D dec := by sorry
