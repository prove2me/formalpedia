-- Prove2me | Theorems.Thm_GeneralPieces_PartA_hasSum_b
-- name    : GeneralPieces.PartA.hasSum_b
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:07.251013+00:00
-- url     : https://prove2.me/theorems/9d98d7ce-c24d-4c16-af3d-87be5c1a43e6
-- title:
--   Part A: has Sum b
-- statement:
--   Σ_{j≥0} 6·2^{j−18(j+1)} = 6·2^{−18}/(1 − 2^{−17}).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L187-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartA.lean#L187-L194

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

theorem GeneralPieces.PartA.hasSum_b : HasSum (fun j : ℕ => (6 : ℝ) * 2 ^ j / 2 ^ (18 * (j + 1))) (6 / 2 ^ 18 * (1 - 1 / 2 ^ 17)⁻¹) := by sorry
