-- Prove2me | Theorems.Thm_FromPrinted_SplitCount_stCOUNTsplitCounts
-- name    : FromPrinted.SplitCount.stCOUNTsplitCounts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:18:09.81045+00:00
-- url     : https://prove2.me/theorems/3638bdd4-5c4c-4c27-954b-40b990fa1385
-- title:
--   Split Count: st COUNTsplit Counts
-- statement:
--   **#k-SAT with the machine named.** For every k ≥ 1 and δ > 0 there are ℓ and τ such that
--   `COUNTsplit k ℓ τ` has polynomial-time steps and writes the number of satisfying assignments of a
--   k-CNF on n variables, in n + 1 bits, within c·2^{δn} steps, on states of size at most c·(length of
--   the input + 1)^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L125-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L125-L142

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

theorem FromPrinted.SplitCount.stCOUNTsplitCounts : StCOUNTsplitCounts := by sorry
