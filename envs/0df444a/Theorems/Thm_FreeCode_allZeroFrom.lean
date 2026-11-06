-- Prove2me | Theorems.Thm_FreeCode_allZeroFrom
-- name    : FreeCode.allZeroFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:16:36.334429+00:00
-- url     : https://prove2.me/theorems/03e74c4b-073e-4223-a955-0e0a246dcc83
-- title:
--   Free Code: all Zero From
-- statement:
--   **Corollary 5 from the two tied statements**, which are hypotheses here: «s_k = 0 for every k ≥ 3.
--   Hence s_∞ = 0, and both ETH and SETH are false», for the numbers s_k defined with the code that does
--   not depend on k. At k = 3 the Turing machine is that of `StTiedThree` («Theorem 2 gives s_3 = 0»),
--   at k > 3 that of `StTied` (the reduction); then the general `SatFree.s_eq_zero_of`. Nothing else is
--   known of the machines.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Main.lean#L111-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Main.lean#L111-L132

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_Order
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Behind
import Definitions.Def_FreeCode_Brute
import Definitions.Def_FreeCode_Tied
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_FreeCode_Main
set_option autoImplicit false
section
section
open FreeCode
open SatFree
open scoped NNReal ENNReal

theorem FreeCode.allZeroFrom : StTiedThree → StTied → SatFree.AllZero := by sorry
