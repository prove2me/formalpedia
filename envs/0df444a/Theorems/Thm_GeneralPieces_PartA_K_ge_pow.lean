-- Prove2me | Theorems.Thm_GeneralPieces_PartA_K_ge_pow
-- name    : GeneralPieces.PartA.K_ge_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:55.771386+00:00
-- url     : https://prove2.me/theorems/57aa2a72-e671-4852-a40c-91340dc6e3dd
-- title:
--   Part A: K ge pow
-- statement:
--   «… and K_ℓ ≥ 2^{18(ℓ+1)}», because x_ℓ ≥ 2^ℓ·x₀ ≥ (ℓ+1)·18.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L138-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L138-L143

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

theorem GeneralPieces.PartA.K_ge_pow (x₀ l : ℕ) (hx : 18 ≤ x₀) : 2 ^ (18 * (l + 1)) ≤ K x₀ l := by sorry
