-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_m_lt_pow
-- name    : GeneralPieces.TopDisplay.m_lt_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:45:29.305186+00:00
-- url     : https://prove2.me/theorems/fb3d3864-11e8-4113-887d-ab7add38add3
-- title:
--   Top Display: m lt pow
-- statement:
--   «By (a), K ≥ m^{1/90}»: if K_{ℓ+1} > m^{1/9} then m < K_ℓ^90.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L44-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L44-L47

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

theorem GeneralPieces.TopDisplay.m_lt_pow (x₀ l m : ℕ) (hx : 1 ≤ x₀) (h : m < K x₀ (l + 1) ^ 9) : m < K x₀ l ^ 90 := by sorry
