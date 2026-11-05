-- Prove2me | Theorems.Thm_GeneralPieces_PartA_thmRunningTime_a
-- name    : GeneralPieces.PartA.thmRunningTime_a
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:35:42.585912+00:00
-- url     : https://prove2.me/theorems/7d0b2c2c-ca24-4690-a553-d2e3cfa14598
-- title:
--   Part A: thm Running Time a
-- statement:
--   Part (a) of Theorem A, for 1/2 ≤ ρ < 1 and every x₀ ≥ 18. It does not need pieces, nor 2^x₀ ≥ c + 5.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L283-L287
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L283-L287

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

theorem GeneralPieces.PartA.thmRunningTime_a (ρ : ℝ) (x₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hx : 18 ≤ x₀) : TheoremAa ρ x₀ := by sorry
