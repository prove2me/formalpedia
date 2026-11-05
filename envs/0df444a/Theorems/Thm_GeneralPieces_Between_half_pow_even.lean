-- Prove2me | Theorems.Thm_GeneralPieces_Between_half_pow_even
-- name    : GeneralPieces.Between.half_pow_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:13.894397+00:00
-- url     : https://prove2.me/theorems/738f23ec-da1a-48c2-b75c-c15bb70a0850
-- title:
--   Between: half pow even
-- statement:
--   (1/√2)^{2j} = 2^{−j}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Between.lean#L40-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Between.lean#L40-L41

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

theorem GeneralPieces.Between.half_pow_even (j : ℕ) : (1 / Real.sqrt 2) ^ (2 * j) = 1 / (2 : ℝ) ^ j := by sorry
