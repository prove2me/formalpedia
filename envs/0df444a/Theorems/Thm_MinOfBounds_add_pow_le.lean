-- Prove2me | Theorems.Thm_MinOfBounds_add_pow_le
-- name    : MinOfBounds.add_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:14:06.109888+00:00
-- url     : https://prove2.me/theorems/3b6b4d03-9db8-4273-b8f5-a9d5c2a44c8c
-- title:
--   Min Of Bounds: add pow le
-- statement:
--   (T + P)^q ≤ 2^q·T^q + 2^q·P^q for all natural numbers: the sum is at most twice the larger of
--   the two.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L44-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L44-L51

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

theorem MinOfBounds.add_pow_le (T P q : ℕ) : (T + P) ^ q ≤ 2 ^ q * T ^ q + 2 ^ q * P ^ q := by sorry
