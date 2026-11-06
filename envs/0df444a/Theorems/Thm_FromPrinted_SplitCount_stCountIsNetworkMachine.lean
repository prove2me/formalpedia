-- Prove2me | Theorems.Thm_FromPrinted_SplitCount_stCountIsNetworkMachine
-- name    : FromPrinted.SplitCount.stCountIsNetworkMachine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:58.787273+00:00
-- url     : https://prove2.me/theorems/e340ca14-0b31-4f56-898d-4dc1fe643da9
-- title:
--   Split Count: st Count Is Network Machine
-- statement:
--   COUNT of Algorithm 1 at level ℓ is line 6 in front of the machine of `StComputesZ` at K = K_ℓ
--   and M = CLIQUE(ℓ): g_ℓ = 3K_ℓ⁸ by definition.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L70-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L70-L70

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_CountDefs
import Definitions.Def_Printed_End
import Definitions.Def_SplitCount_StepOne
import Definitions.Def_SplitCount_Main
import Definitions.Def_SplitCount_Tree
import Definitions.Def_SplitCount_Suffices
import Definitions.Def_SplitCount_Cert
import Definitions.Def_SplitCount_Host
import Definitions.Def_CountKSat_Host
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_CountKSat_EndLemmas
import Definitions.Def_Eight_SecPseudocode_Levels
import Definitions.Def_WidthK_Decode
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Count
import Theorems.Thm_SplitCount_stCountIsNetworkMachine

set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem FromPrinted.SplitCount.stCountIsNetworkMachine : StCountIsNetworkMachine := by sorry
