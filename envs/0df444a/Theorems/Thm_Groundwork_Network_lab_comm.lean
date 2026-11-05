-- Prove2me | Theorems.Thm_Groundwork_Network_lab_comm
-- name    : Groundwork.Network.lab_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:41:57.556866+00:00
-- url     : https://prove2.me/theorems/a364c021-a294-4920-8fec-ffb54a2b652b
-- title:
--   Network: lab comm
-- statement:
--   The label set of a pair does not depend on the order of the two nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L72-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Groundwork/Net/Net.lean#L72-L73

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
open Groundwork.Network

theorem Groundwork.Network.lab_comm [LinearOrder J] (N : Network J σ τ) (a b : J) : N.lab a b = N.lab b a := by sorry
