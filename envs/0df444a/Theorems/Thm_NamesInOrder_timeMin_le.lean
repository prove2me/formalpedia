-- Prove2me | Theorems.Thm_NamesInOrder_timeMin_le
-- name    : NamesInOrder.timeMin_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:59:20.149933+00:00
-- url     : https://prove2.me/theorems/1cf92fc5-437f-4870-b19d-036866d8bd26
-- title:
--   Names In Order: time Min le
-- statement:
--   2^{C·min{a, b}}, rounded down, is at most each of 2^{C·a} and 2^{C·b}, rounded down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/General.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/General.lean#L35-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Main
import Definitions.Def_MinOfBounds_Rename
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_Wrap_Main
import Definitions.Def_Wrap_Sim
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_NamesInOrder_General
set_option autoImplicit false
section
section
open NamesInOrder
open Turing Groundwork Wrap TwoMachines MainTheoremForms MinOfBounds
open Sat3 (CNF)

theorem NamesInOrder.timeMin_le (C k m n : ℕ) : timeMin C k m n ≤ timeM C k m ∧ timeMin C k m n ≤ timeN C k n := by sorry
