-- Prove2me | Theorems.Thm_MinOfBounds_bound_le_timeM
-- name    : MinOfBounds.bound_le_timeM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:13:01.955204+00:00
-- url     : https://prove2.me/theorems/f3409333-e031-494f-8a33-b8bd2b4ed3ee
-- title:
--   Min Of Bounds: bound le time M
-- statement:
--   The bound of `AppRunningTime.BoundInM` with the constant C, C·2^{C·km/√(log₂(m+2))} rounded
--   down, is at most 2^{3C·km/√(log m)} rounded down; for k ≥ 1 and m ≥ 2. The factor C in front goes
--   into the exponent because km/√(log m) is at least 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L147-L153
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L147-L153

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

theorem MinOfBounds.bound_le_timeM (C : ℕ) {k m : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) : SatM.bound (SatM.rPow (1 / 2)) C k m ≤ timeM (3 * C) k m := by sorry
