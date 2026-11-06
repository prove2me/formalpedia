-- Prove2me | Theorems.Thm_FreeCode_sum_satAt_pos
-- name    : FreeCode.sum_satAt_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:30:26.997186+00:00
-- url     : https://prove2.me/theorems/13bd270f-caa6-4512-af4b-69d59b39db33
-- title:
--   Free Code: sum sat At pos
-- statement:
--   The number of y < 2^n that pass the test is positive exactly if φ is satisfiable.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean#L43-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean#L43-L60

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
set_option autoImplicit false
section
section
open FreeCode
open Groundwork Groundwork.Prog Paper SplitSat

theorem FreeCode.sum_satAt_pos {n : ℕ} (φ : Sat3.CNF n) :
    0 < ∑ y ∈ Finset.range (2 ^ n), ((PaddedDescent.satAt (Decode.toN φ) y).toNat : ℤ) ↔ Sat3.Satisfiable φ := by sorry
