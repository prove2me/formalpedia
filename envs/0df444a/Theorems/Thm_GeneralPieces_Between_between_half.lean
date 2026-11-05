-- Prove2me | Theorems.Thm_GeneralPieces_Between_between_half
-- name    : GeneralPieces.Between.between_half
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:24:29.836352+00:00
-- url     : https://prove2.me/theorems/1dedccf1-c416-4a42-a0e8-aaa3fe68fd5a
-- title:
--   Between: between half
-- statement:
--   0.85·(1/√2)^ℓ ≤ num ℓ/den ℓ ≤ (1/√2)^ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Between.lean#L44-L73
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Between.lean#L44-L73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_GeneralPieces_Num_Between
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Between
open Groundwork PaddedDescent.F Levels.Gen

theorem GeneralPieces.Between.between_half (l : ℕ) : 0.85 * (1 / Real.sqrt 2) ^ l ≤ (num l : ℝ) / (den l : ℝ) ∧ (num l : ℝ) / (den l : ℝ) ≤ (1 / Real.sqrt 2) ^ l := by sorry
