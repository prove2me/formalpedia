-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_needTop_le_display
-- name    : GeneralPieces.TopDisplay.needTop_le_display
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:49:40.67634+00:00
-- url     : https://prove2.me/theorems/3f8b7cdf-7c01-4e77-86fe-75a1a203d4fd
-- title:
--   Top Display: need Top le display
-- statement:
--   The display for the exponent of the algorithm of this development: at an index i with K⁹ ≤ m, 0
--   ≤ e ≤ 1 and the bound of part (b),
--   `needTop` ≤ 2ekm + A·(km/K + K⁸·log K + K²·log(km)) with A = 2C₀ + 15.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L154-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L154-L197

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

theorem GeneralPieces.TopDisplay.needTop_le_display {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hm : S.K i ^ 9 ≤ m)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ 2 * e * k * m + (2 * C₀ + 15 : ℕ) *
      ((k : ℝ) * m / S.K i + (S.K i : ℝ) ^ 8 * Real.logb 2 (S.K i) + (S.K i : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) := by sorry
