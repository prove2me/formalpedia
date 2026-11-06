-- Prove2me | Theorems.Thm_FromPrinted_FreeCode_allZeroFrom
-- name    : FromPrinted.FreeCode.allZeroFrom
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:17:12.683531+00:00
-- url     : https://prove2.me/theorems/28c283f4-8cbc-4076-b424-f6c778492090
-- title:
--   Free Code: all Zero From
-- statement:
--   **Corollary 5 from the two tied statements**, which are hypotheses here: «s_k = 0 for every k ≥ 3.
--   Hence s_∞ = 0, and both ETH and SETH are false», for the numbers s_k defined with the code that does
--   not depend on k. At k = 3 the Turing machine is that of `StTiedThree` («Theorem 2 gives s_3 = 0»),
--   at k > 3 that of `StTied` (the reduction); then the general `SatFree.s_eq_zero_of`. Nothing else is
--   known of the machines.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/FreeCode.lean#L87-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/FreeCode.lean#L87-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_SatDefs
import Definitions.Def_FromPrinted_Core
import Definitions.Def_FreeCode_Reader
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Random
import Definitions.Def_FreeCode_Tied
import Definitions.Def_FreeCode_Main
import Definitions.Def_SplitSat_Walk
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Main
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Mathlib.Tactic
import Definitions.Def_FromPrinted_FreeCode
import Theorems.Thm_FreeCode_allZeroFrom
import Theorems.Thm_SplitSat_endFrom
import Theorems.Thm_SplitSat_eth_and_seth_false
import Theorems.Thm_SplitSat_stSATsplit
import Theorems.Thm_SplitSat_stTiedTM
import Theorems.Thm_SplitSat_stTiedThreeTM

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog WidthK.Prog UniformInK Paper FreeCode SatFree
open SplitSat hiding core3 StCore3Eq StCore3 SATsplit StSATsplit StTiedTM StTiedThreeTM ThreeSatStatement stSATsplit stTiedTM stTiedThreeTM endFrom eth_and_seth_false
open FromPrinted.SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.FreeCode

theorem FromPrinted.FreeCode.allZeroFrom : StTiedThree → StTied → SatFree.AllZero := by sorry
