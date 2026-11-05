-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_needTop_le_main
-- name    : GeneralPieces.TopDisplay.needTop_le_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:25.014439+00:00
-- url     : https://prove2.me/theorems/d09de880-3077-4f07-b400-c78b5017ced7
-- title:
--   Top Display: need Top le main
-- statement:
--   The exponent of the algorithm of this development is at most 2ekm + A'·k·m^{1−1/90} with A' =
--   203·(2C₀ + 15), at an index with m^{1/90} ≤ K ≤ m^{1/9}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L329-L340
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L329-L340

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

theorem GeneralPieces.TopDisplay.needTop_le_main {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hm : S.K i ^ 9 ≤ m) (hm' : m ≤ S.K i ^ 90)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ 2 * e * k * m + (203 * (2 * C₀ + 15) : ℕ) * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by sorry
