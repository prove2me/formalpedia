-- Prove2me | Theorems.Thm_FromPrinted_SplitSat_stSATsplit
-- name    : FromPrinted.SplitSat.stSATsplit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T12:00:57.949202+00:00
-- url     : https://prove2.me/theorems/4cb9d3bb-ac31-4d54-8a5b-bba4684f66ec
-- title:
--   Split Sat: st SATsplit
-- statement:
--   **k-SAT with the machine named**: for every k ≥ 3 and δ > 0 there are τ, ℓ₃, τ₃ such that
--   `SATsplit k τ ℓ₃ τ₃`, the reduction run on the machine of Theorem 2 in its decision form without its
--   reader, has polynomial-time steps and decides k-SAT with the exponent δ. This is the statement
--   `FromPrinted.SplitSat.StSATsplit`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L47-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/SplitSat.lean#L47-L50

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
import Theorems.Thm_SplitSat_stSATsplit

set_option autoImplicit false
section
section
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping SplitSat
open scoped NNReal ENNReal
open FromPrinted FromPrinted.SplitSat

theorem FromPrinted.SplitSat.stSATsplit : StSATsplit := by sorry
