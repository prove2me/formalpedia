-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_one_le_mul_root
-- name    : GeneralPieces.TopDisplay.one_le_mul_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:33:56.048876+00:00
-- url     : https://prove2.me/theorems/485c6b2e-9ef3-4791-82c9-f06f202325be
-- title:
--   Top Display: one le mul root
-- statement:
--   m^{−1/(9d)} is small against e: if K ≤ t^d and e ≥ (log K)^{−C₀}, then 1 ≤
--   d^{C₀}·C₀!·2^{C₀}·e·t.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L363-L379
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L363-L379

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

theorem GeneralPieces.TopDisplay.one_le_mul_root (K C₀ d : ℕ) (t e : ℝ) (ht : 1 ≤ t) (hK : 2 ≤ K) (hKt : (K : ℝ) ≤ t ^ d) (he : 1 / Real.logb 2 K ^ C₀ ≤ e) :
    1 ≤ ((d ^ C₀ * (C₀.factorial * 2 ^ C₀) : ℕ) : ℝ) * e * t := by sorry
