-- Prove2me | Theorems.Thm_GeneralPieces_PartA_x_formula
-- name    : GeneralPieces.PartA.x_formula
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:56.883203+00:00
-- url     : https://prove2.me/theorems/27445367-924a-43fd-b73f-34c8bc68178e
-- title:
--   Part A: x formula
-- statement:
--   «… which gives the formula by induction»: x_ℓ = (3x₀+6)·2^ℓ − 6ℓ − 2x₀ − 6.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L39-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L39-L42

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

theorem GeneralPieces.PartA.x_formula (x₀ l : ℕ) : (x x₀ l : ℝ) = (3 * x₀ + 6) * 2 ^ l - 6 * l - 2 * x₀ - 6 := by sorry
