-- Prove2me | Theorems.Thm_MinOfBounds_min_time_le
-- name    : MinOfBounds.min_time_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:38:39.826636+00:00
-- url     : https://prove2.me/theorems/8122df95-d7c3-4445-bf7c-950c1aec21bb
-- title:
--   Min Of Bounds: min time le
-- statement:
--   The smaller of the times 2^{C₁·km/√(log m)} and 2^{C₂·k²·n·log log n/√(log n)} is at most
--   2^{D·X}, where D is the larger of C₁ and C₂ and X is the smaller of the two exponents km/√(log m)
--   and k²·n·log log n/√(log n); for k ≥ 1, m ≥ 2 and n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L56-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L56-L68

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

theorem MinOfBounds.min_time_le (C₁ C₂ : ℕ) {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) :
    ((min (timeM C₁ k m) (timeN C₂ k n) : ℕ) : ℝ) ≤ (2 : ℝ) ^ (((max C₁ C₂ : ℕ) : ℝ) * min (expM k m) (expN k n)) := by sorry
