-- Prove2me | Theorems.Thm_FromPrinted_SplitCount_countingCorollary
-- name    : FromPrinted.SplitCount.countingCorollary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:03.6575+00:00
-- url     : https://prove2.me/theorems/5347a750-3168-43a2-a01b-6870aaf8fc90
-- title:
--   Split Count: counting Corollary
-- statement:
--   **Corollary 6**, in the wording of PaperSentencesStatement.lean: `endFrom` on the proof
--   `stTiedTM` of the tied statement.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L182-L182
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L182-L182

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
set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem FromPrinted.SplitCount.countingCorollary : ThreeSatStatement := by sorry
