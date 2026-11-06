-- Prove2me | Theorems.Thm_MainRoute_steps_le_of_exponent_le
-- name    : MainRoute.steps_le_of_exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:12:29.473448+00:00
-- url     : https://prove2.me/theorems/c0436b35-b992-4e3e-89fe-1630f4a3fe10
-- title:
--   Main Route: steps le of exponent le
-- statement:
--   The numbers: if E ≤ G·X with X ≥ 1, then q·(L + 2^E + 1)^q ≤ ⌊2^(C·X)⌋ + C·L^C for L ≥ 1, with C =
--   2q + 2q(G + 1) + q·4^q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/EveryMachine.lean#L36-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MainRoute/EveryMachine.lean#L36-L67

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainRoute_Defs
import Definitions.Def_RecursionWithPieces_Main
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_VariableBound_Paper_Rename_Time
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_MainRoute_EveryMachine
set_option autoImplicit false
section
section
open MainRoute
open Turing Groundwork PaddedDescent PaddedDescent.F ClauseBound.Alg Wrap TwoMachines MainTheoremForms MinOfBounds PairsToBound
open Sat3 (CNF)

theorem MainRoute.steps_le_of_exponent_le (q G : ℕ) {E L : ℕ} {X : ℝ} (hX : 1 ≤ X) (hE : (E : ℝ) ≤ G * X) (hL : 1 ≤ L) :
    q * (L + 2 ^ E + 1) ^ q ≤ ⌊(2 : ℝ) ^ (((2 * q + 2 * q * (G + 1) + q * 4 ^ q : ℕ) : ℝ) * X)⌋₊ + (2 * q + 2 * q * (G + 1) + q * 4 ^ q) * L ^ (2 * q + 2 * q * (G + 1) + q * 4 ^ q) := by sorry
