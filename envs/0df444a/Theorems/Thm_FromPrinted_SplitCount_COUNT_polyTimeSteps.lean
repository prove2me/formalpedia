-- Prove2me | Theorems.Thm_FromPrinted_SplitCount_COUNT_polyTimeSteps
-- name    : FromPrinted.SplitCount.COUNT_polyTimeSteps
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:38:13.198091+00:00
-- url     : https://prove2.me/theorems/fdf70c0b-9cfc-4988-a3bc-7a2cef6c7ee0
-- title:
--   Split Count: COUNT poly Time Steps
-- statement:
--   The steps of COUNT of Algorithm 1 are polynomial time, at every level ℓ: those of CLIQUE(ℓ) are
--   (`Printed.stClique`), so those of the machine of Lemma 1 made from it (`Printed.stGroupingPoly`), so
--   those of that machine on the network of Φ (`Printed.onFormula_poly`), and line 6 keeps this
--   (`Printed.firstLine_poly`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L87-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L87-L88

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
import Theorems.Thm_Exits_COUNT_polyTimeSteps

set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem FromPrinted.SplitCount.COUNT_polyTimeSteps (ℓ : ℕ) : PolyTimeSteps (Printed.COUNT ℓ) := by sorry
