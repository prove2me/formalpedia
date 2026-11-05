-- Prove2me | Theorems.Thm_MinOfBounds_factor_goes_into_exponent
-- name    : MinOfBounds.factor_goes_into_exponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:12:23.951619+00:00
-- url     : https://prove2.me/theorems/0dff8331-3666-49f0-9208-d400a2d20aaa
-- title:
--   Min Of Bounds: factor goes into exponent
-- statement:
--   On real numbers: if T ≤ 2^{D·X} and X ≥ 2, then q·(2^q·T^q) ≤ 2^{(q·D + q)·X}. Here X ≥ 2 is
--   used: q·2^q ≤ 2^{2q} ≤ 2^{q·X}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L72-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L72-L92

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

theorem MinOfBounds.factor_goes_into_exponent (q D T : ℕ) {X : ℝ} (hX : 2 ≤ X) (hT : (T : ℝ) ≤ (2 : ℝ) ^ ((D : ℝ) * X)) :
    (q : ℝ) * ((2 : ℝ) ^ q * (T : ℝ) ^ q) ≤ (2 : ℝ) ^ (((q : ℝ) * D + q) * X) := by sorry
