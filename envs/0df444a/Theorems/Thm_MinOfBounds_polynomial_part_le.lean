-- Prove2me | Theorems.Thm_MinOfBounds_polynomial_part_le
-- name    : MinOfBounds.polynomial_part_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:12:44.95577+00:00
-- url     : https://prove2.me/theorems/382f9be7-31ad-4e1d-be94-12eedd8f4ff8
-- title:
--   Min Of Bounds: polynomial part le
-- statement:
--   The polynomial part: for L ≥ 1 and L₁ ≤ a·L^a, q·2^q·(C₁·L₁^C₁ + L + 1)^q is at most
--   q·2^q·(C₁·a^C₁ + 2)^q times L^((a·C₁ + 1)·q).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L109-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L109-L123

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

theorem MinOfBounds.polynomial_part_le (C₁ q a : ℕ) {L L₁ : ℕ} (hL : 1 ≤ L) (h : L₁ ≤ a * L ^ a) :
    q * (2 ^ q * (C₁ * L₁ ^ C₁ + L + 1) ^ q) ≤ q * 2 ^ q * (C₁ * a ^ C₁ + 2) ^ q * L ^ ((a * C₁ + 1) * q) := by sorry
