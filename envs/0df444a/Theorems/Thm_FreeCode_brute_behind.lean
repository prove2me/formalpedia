-- Prove2me | Theorems.Thm_FreeCode_brute_behind
-- name    : FreeCode.brute_behind
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:29:53.74985+00:00
-- url     : https://prove2.me/theorems/e0fa642d-66c7-4114-b95a-bd2e8ade0c1a
-- title:
--   Free Code: brute behind
-- statement:
--   Exhaustive search behind any reader of the code: on the code of a k-CNF on n variables it ends
--   after 2·2^n steps with the bit that says whether φ is satisfiable, on states of size at most
--   c·(n+2)^c, where c = 2·(2^k·(2k+1) + 3) + k + 16.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean#L114-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean#L114-L131

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

theorem FreeCode.brute_behind {dec : List Bool → List Unit × Fml} (hdec : Reads dec) (k : ℕ) (n : ℕ) (φ : Sat3.CNF n) (h3 : SatK.IsKCNF k φ) :
    ∃ b : Bool, (Stepped.mapIn dec bruteCore).Runs (SatFree.enc φ) (2 * 2 ^ n)
      ((2 * (2 ^ k * (2 * k + 1) + 3) + k + 16) * (n + 2) ^ (2 * (2 ^ k * (2 * k + 1) + 3) + k + 16)) b ∧ (b = true ↔ Sat3.Satisfiable φ) := by sorry
