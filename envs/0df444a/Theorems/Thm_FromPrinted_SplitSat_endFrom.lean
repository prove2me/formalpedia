-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_endFrom
-- name    : FromPrinted.SplitSat.endFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:33:41.63183+00:00
-- url     : https://prove2.me/theorems/efc7fd64-a638-4b47-baf8-98a02c5837c1
-- title:
--   Split Sat: end From
-- statement:
--   **Corollary 5 from the two tied statements**, which are hypotheses here: «s_k = 0 for every k ≥ 3.
--   Hence s_∞ = 0, and both ETH and SETH are false.» At k = 3 the Turing machine is that of
--   `StTiedThreeTM` («Theorem 2 gives s_3 = 0»), at k > 3 that of `StTiedTM` (the reduction); then the
--   general `SatK.sTM_eq_zero_of`. Nothing else is known of the machines.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L79-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L79-L101

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_Printed_End
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SplitSat_Main
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_FromPrinted_SplitSat
import Theorems.Thm_SplitSat_endFrom

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat

theorem FromPrinted.SplitSat.endFrom : StTiedTM → StTiedThreeTM → ThreeSatStatement := by sorry
