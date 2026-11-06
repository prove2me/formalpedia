-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_eth_and_seth_false
-- name    : FromPrinted.SplitSat.eth_and_seth_false
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:10:21.457023+00:00
-- url     : https://prove2.me/theorems/c8d9c8ca-d94f-4a74-8a2e-253c607a1ca9
-- title:
--   Split Sat: eth and seth false
-- statement:
--   **Corollary 5**: «s_k = 0 for every k ≥ 3. Hence s_∞ = 0, and both ETH and SETH are false.» The
--   statement is `PaperSentences.CorEth` of PaperSentencesStatement.lean. It is `endFrom` applied to
--   `stTiedTM` (the cited reduction of k-SAT to 3-SAT) and `stTiedThreeTM` (Theorem 2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L106-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L106-L106

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
import Theorems.Thm_SplitSat_eth_and_seth_false

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat

theorem FromPrinted.SplitSat.eth_and_seth_false : ThreeSatStatement := by sorry
