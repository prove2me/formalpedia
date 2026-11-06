-- Prove2me | Theorems.Thm_FromPrinted_SplitCount_stComputesZ
-- name    : FromPrinted.SplitCount.stComputesZ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:49.806194+00:00
-- url     : https://prove2.me/theorems/3204d8fd-28cd-4776-9035-8f88f9e5d3b7
-- title:
--   Split Count: st Computes Z
-- statement:
--   **The proof of Theorem 2, with K and g chosen from δ' as there, computes Z.** For 0 < δ' ≤ 1, K
--   ≥ 2 with K ≥ 72/δ', g = 3K⁸ and any machine M for cliques on K nodes with
--   `Printed.AchievedBy M Cc K (δ'/12)`, the algorithm of the printed proof of Lemma 1 with M, run on
--   the network of Φ on g clusters, computes Z as Section 6 says.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L55-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Count.lean#L55-L61

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
import Theorems.Thm_SplitCount_stComputesZ

set_option autoImplicit false
section
section
open SplitCount
open FromPrinted FromPrinted.SplitCount
open Groundwork Groundwork.Prog Paper CountKSat Eight Eight.ViaGrouping Occ
open scoped NNReal

theorem FromPrinted.SplitCount.stComputesZ : StComputesZ := by sorry
