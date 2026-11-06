-- Prove2me | Theorems.Thm_FreeCode_stBrute
-- name    : FreeCode.stBrute
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:57:57.583552+00:00
-- url     : https://prove2.me/theorems/6edbd2ef-33d0-4537-9489-15f86a778229
-- title:
--   Free Code: st Brute
-- statement:
--   **«Trying all assignments».** The reader `readFree` and one Turing machine with finite
--   alphabets: exhaustive search behind the reader has polynomial-time steps and decides k-SAT, for
--   every k, within c·2^n steps on states of size at most c·(n+2)^c; the Turing machine simulates it
--   with polynomial overhead, and decides k-SAT, for every k, within c·(n+2)^c·2^n steps. This is the
--   statement `FreeCode.StBrute`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean#L138-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FreeCode/Brute.lean#L138-L164

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

theorem FreeCode.stBrute : StBrute := by sorry
