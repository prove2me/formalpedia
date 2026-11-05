-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_K_ge_root90
-- name    : GeneralPieces.TopDisplay.K_ge_root90
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:16.365196+00:00
-- url     : https://prove2.me/theorems/9c6a3a63-2e56-48f3-bbda-d7cf6adff71a
-- title:
--   Top Display: K ge root90
-- statement:
--   «By (a), K ≥ m^{1/90}», for the largest ℓ with K_ℓ ≤ m^{1/9}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L56-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA

theorem GeneralPieces.TopDisplay.K_ge_root90 (x₀ l m : ℕ) (hx : 1 ≤ x₀) (h : m < K x₀ (l + 1) ^ 9) : (m : ℝ) ^ (1 / 90 : ℝ) ≤ K x₀ l := by sorry
