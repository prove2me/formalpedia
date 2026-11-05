-- Prove2me | Theorems.Thm_MinOfBounds_timeCor_mono
-- name    : MinOfBounds.timeCor_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:13:42.195785+00:00
-- url     : https://prove2.me/theorems/43146b26-bc2a-4e4e-9803-6a6d9dcb2c23
-- title:
--   Min Of Bounds: time Cor mono
-- statement:
--   The time of Corollary 11 grows with the constant; for k ≥ 1, m ≥ 2 and n ≥ 4.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L126-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/MinOfBounds/Arith.lean#L126-L128

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

theorem MinOfBounds.timeCor_mono {C C' : ℕ} (h : C ≤ C') {k m n : ℕ} (hk : 1 ≤ k) (hm : 2 ≤ m) (hn : 4 ≤ n) : timeCor C k m n ≤ timeCor C' k m n := by sorry
