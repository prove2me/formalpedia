-- Prove2me | Theorems.Thm_GeneralPieces_PartA_exp_tsum_le
-- name    : GeneralPieces.PartA.exp_tsum_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:31.939378+00:00
-- url     : https://prove2.me/theorems/fb80343a-b930-4e5f-84b2-e414ba629531
-- title:
--   Part A: exp tsum le
-- statement:
--   «… ≤ e^{1/2}·0.51».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L211-L214
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L211-L214

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_LevelsStatement
import Definitions.Def_ClauseBound_Gen_PartA
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Num_PartA
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartA
open Finset Levels.Gen ClauseBound.Gen

theorem GeneralPieces.PartA.exp_tsum_le : Real.exp (∑' j : ℕ, (1 : ℝ) / 2 ^ (j + 2)) * (1 / 2 + ∑' j : ℕ, (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) ≤
    Real.exp (1 / 2) * 0.51 := by sorry
