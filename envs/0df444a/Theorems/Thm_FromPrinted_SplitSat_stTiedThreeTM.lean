-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_stTiedThreeTM
-- name    : FromPrinted.SplitSat.stTiedThreeTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T11:54:38.89719+00:00
-- url     : https://prove2.me/theorems/7d5aa032-fc2f-475f-8495-5cf54157610c
-- title:
--   Split Sat: st Tied Three TM
-- statement:
--   **«Theorem 2 gives s_3 = 0», tied to the machine of Theorem 2 in its decision form**: for every
--   δ > 0 there are ℓ, τ such that `Printed.SAT ℓ τ` itself has polynomial-time steps and decides 3-SAT
--   with the exponent δ, a Turing machine M with finite alphabets simulates it with polynomial overhead,
--   and M decides 3-SAT within ⌊c·2^{δn}⌋ steps. This is the statement
--   `FromPrinted.SplitSat.StTiedThreeTM`; ℓ and τ are those that `Printed.stDecides` gives for δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L68-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L68-L73

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
import Theorems.Thm_SplitSat_stTiedThreeTM

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat

theorem FromPrinted.SplitSat.stTiedThreeTM : StTiedThreeTM := by sorry
