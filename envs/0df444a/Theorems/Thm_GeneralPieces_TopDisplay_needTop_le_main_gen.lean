-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_needTop_le_main_gen
-- name    : GeneralPieces.TopDisplay.needTop_le_main_gen
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:34:56.464839+00:00
-- url     : https://prove2.me/theorems/d4a0f458-cb76-4d4b-ad6a-1cd19724af20
-- title:
--   Top Display: need Top le main gen
-- statement:
--   The exponent of the algorithm of this development is at most 2ekm + A'·k·m^{1−1/(9d)} with A' =
--   (3 + 20d)·(2C₀ + 15), at an index with m^{1/(9d)} ≤ K ≤ m^{1/9}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L314-L325
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L314-L325

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

theorem GeneralPieces.TopDisplay.needTop_le_main_gen {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m d : ℕ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hd : 2 ≤ d) (hm : S.K i ^ 9 ≤ m) (hm' : m ≤ S.K i ^ (9 * d))
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ 2 * e * k * m + ((3 + 20 * d) * (2 * C₀ + 15) : ℕ) * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ))) := by sorry
