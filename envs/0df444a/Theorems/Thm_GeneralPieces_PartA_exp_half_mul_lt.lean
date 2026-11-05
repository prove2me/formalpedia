-- Prove2me | Theorems.Thm_GeneralPieces_PartA_exp_half_mul_lt
-- name    : GeneralPieces.PartA.exp_half_mul_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:33.659149+00:00
-- url     : https://prove2.me/theorems/a20dbd6c-020e-4df2-92e4-daadefc59516
-- title:
--   Part A: exp half mul lt
-- statement:
--   «… < 0.85».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L217-L225
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L217-L225

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

theorem GeneralPieces.PartA.exp_half_mul_lt : Real.exp (1 / 2) * 0.51 < 0.85 := by sorry
