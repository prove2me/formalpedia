-- Prove2me | Theorems.Thm_MinOfBounds_overheadGoesIntoC
-- name    : MinOfBounds.overheadGoesIntoC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:38:31.51729+00:00
-- url     : https://prove2.me/theorems/464d4da7-46ad-449e-ac67-1b3022c2f0f2
-- title:
--   Min Of Bounds: overhead Goes Into C
-- statement:
--   «… as km/√(log m) and n·log log n/√(log n) are at least 2, this constant goes into C.» The
--   constant is C = (q·max(C₁, C₂) + q) + q·2^q·(C₁·a^C₁ + 2)^q + (a·C₁ + 1)·q.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L132-L142
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L132-L142

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

theorem MinOfBounds.overheadGoesIntoC : OverheadGoesIntoC := by sorry
