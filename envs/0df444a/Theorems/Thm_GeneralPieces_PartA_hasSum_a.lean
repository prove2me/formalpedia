-- Prove2me | Theorems.Thm_GeneralPieces_PartA_hasSum_a
-- name    : GeneralPieces.PartA.hasSum_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:53.348781+00:00
-- url     : https://prove2.me/theorems/db4866ff-3acc-4960-a804-a0975a9c2472
-- title:
--   Part A: has Sum a
-- statement:
--   Σ_{j≥0} 2^{−j−2} = 1/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L178-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L178-L184

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

theorem GeneralPieces.PartA.hasSum_a : HasSum (fun j : ℕ => (1 : ℝ) / 2 ^ (j + 2)) (1 / 2) := by sorry
