-- Prove2me | Theorems.Thm_GeneralPieces_PartA_logK_formula
-- name    : GeneralPieces.PartA.logK_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:16.196014+00:00
-- url     : https://prove2.me/theorems/edb93352-ddfa-4593-9674-fc7bb8aa2ddf
-- title:
--   Part A: log K formula
-- statement:
--   The first assertion of part (a): log K_ℓ = (3x₀+6)·2^ℓ − 6ℓ − 2x₀ − 6.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L45-L46
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L45-L46

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

theorem GeneralPieces.PartA.logK_formula (x₀ l : ℕ) : Real.logb 2 (K x₀ l) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6 := by sorry
