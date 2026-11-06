-- Prove2me | Theorems.Thm_FromPrinted_SplitCount_endFrom
-- name    : FromPrinted.SplitCount.endFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:14.815753+00:00
-- url     : https://prove2.me/theorems/3a734761-7ba6-4488-ab92-a1f146b99e0f
-- title:
--   Split Count: end From
-- statement:
--   **Corollary 6**: «For every k ≥ 3 and δ > 0 there is a deterministic algorithm that computes the
--   number of satisfying assignments of a k-CNF on n variables in time O(2^{δn}). For k = 3 this says
--   that the counting version #ETH of ETH is false.»
--   The statement is `PaperSentences.CorCounting` of PaperSentencesStatement.lean, for Turing machines.
--   Here it is drawn from the tied statement `StTiedTM` as a hypothesis: both halves take the Turing
--   machine of that statement, which simulates `COUNTsplit k ℓ τ`; the second half at k = 3, by
--   `CountKSat.EndLemmas.not_CountETH_TM_of`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L173-L178
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L173-L178

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
import Theorems.Thm_SplitCount_endFrom

set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem FromPrinted.SplitCount.endFrom (h : StTiedTM) : ThreeSatStatement := by sorry
