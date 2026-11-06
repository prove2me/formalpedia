-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_stTiedTM
-- name    : FromPrinted.SplitSat.stTiedTM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:08:01.085742+00:00
-- url     : https://prove2.me/theorems/27a0b4ba-507f-4fd2-a0d1-a7e5c208f69a
-- title:
--   Split Sat: st Tied TM
-- statement:
--   **Tied to the machine, on Mathlib's Turing machines**: for every k ≥ 3 and δ > 0 there are τ,
--   ℓ₃, τ₃ such that `SATsplit k τ ℓ₃ τ₃` itself has polynomial-time steps and decides k-SAT with the
--   exponent δ, a Turing machine M with finite alphabets simulates it with polynomial overhead, and M
--   decides k-SAT within ⌊c·2^{δn}⌋ steps. This is the statement `FromPrinted.SplitSat.StTiedTM`. In the
--   proof the named machine has the exponent δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L57-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L57-L61

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
import Theorems.Thm_SplitSat_stTiedTM

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat

theorem FromPrinted.SplitSat.stTiedTM : StTiedTM := by sorry
