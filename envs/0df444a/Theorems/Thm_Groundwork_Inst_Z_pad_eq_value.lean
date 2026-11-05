-- Prove2me | Theorems.Thm_Groundwork_Inst_Z_pad_eq_value
-- name    : Groundwork.Inst.Z_pad_eq_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:13:47.525567+00:00
-- url     : https://prove2.me/theorems/65196625-b818-4d99-a6b8-4ab1dd6e1ca6
-- title:
--   Inst: Z pad eq value
-- statement:
--   The padded instance has the value of the network of the instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L160-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L160-L164

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

theorem Groundwork.Inst.Z_pad_eq_value [Fintype J] [LinearOrder J] [Fintype A] [DecidableEq A] [Fintype A'] [DecidableEq A']
    (R : Inst J A) (d : A) (d' : A') (D : Finset A') (dec : A' → A) (h : Set.BijOn dec D Set.univ) :
    (R.pad d D dec).Z d' = (R.net d).value := by sorry
