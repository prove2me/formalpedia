-- Prove2me | Theorems.Thm_FreeCode_satAt_toN
-- name    : FreeCode.satAt_toN
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:27:55.204431+00:00
-- url     : https://prove2.me/theorems/b766d395-3bb9-4348-8cb4-c53f59057244
-- title:
--   Free Code: sat At to N
-- statement:
--   The assignment that gives xᵢ the i-th binary digit of y passes the test of exhaustive search
--   exactly if it makes a literal of every clause true.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean#L39-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean#L39-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FreeCode_Defs
import Definitions.Def_FreeCode_Code
import Definitions.Def_FreeCode_ReaderCert
import Definitions.Def_FreeCode_Behind
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Basic
import Batteries.Data.Nat.Lemmas
import Mathlib.Tactic
import Definitions.Def_FreeCode_Brute
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat

theorem FreeCode.satAt_toN {n : ℕ} (φ : Sat3.CNF n) (y : ℕ) : PaddedDescent.satAt (Decode.toN φ) y = true ↔ ∀ C ∈ φ, ∃ l ∈ C, y.testBit l.1.val = l.2 := by sorry
