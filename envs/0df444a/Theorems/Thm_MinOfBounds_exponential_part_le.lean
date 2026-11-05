-- Prove2me | Theorems.Thm_MinOfBounds_exponential_part_le
-- name    : MinOfBounds.exponential_part_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:13:38.530013+00:00
-- url     : https://prove2.me/theorems/87cd5f86-ce94-4a90-af0b-64ff846b9642
-- title:
--   Min Of Bounds: exponential part le
-- statement:
--   The exponential part: q·2^q·T^q, where T is the smaller of the two times with the constants C₁
--   and C₂, is at most the time of Corollary 11 with the constant q·max(C₁, C₂) + q; for k ≥ 1, m ≥ 2
--   and n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L97-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L97-L105

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MinOfBounds_Defs
import Definitions.Def_VariableBound_Paper_Arith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_MinOfBounds_Arith
set_option autoImplicit false
section
section
open MinOfBounds
open MainTheoremForms VariableBound.Paper

theorem MinOfBounds.exponential_part_le (C₁ C₂ q : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    q * (2 ^ q * min (timeM C₁ k m) (timeN C₂ k n) ^ q) ≤ timeCor (q * max C₁ C₂ + q) k m n := by sorry
