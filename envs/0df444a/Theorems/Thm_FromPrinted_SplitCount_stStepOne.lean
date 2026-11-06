-- Prove2me | Theorems.Thm_FromPrinted_SplitCount_stStepOne
-- name    : FromPrinted.SplitCount.stStepOne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:03:15.725097+00:00
-- url     : https://prove2.me/theorems/9618e851-1459-4b53-b979-c7150c970595
-- title:
--   Split Count: st Step One
-- statement:
--   **The count of a 3-CNF by COUNT of Algorithm 1.** For 0 < δ' ≤ 1 and every level ℓ with K_ℓ ≥
--   72/δ' and e_ℓ ≤ δ'/12, `countThree ℓ` computes the number Z·2^{n'} of the proof of Corollary 6, in
--   the form that `SplitCount.stStepOneFor` states.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L75-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L75-L81

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
import Theorems.Thm_SplitCount_stStepOne

set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem FromPrinted.SplitCount.stStepOne : StStepOne := by sorry
