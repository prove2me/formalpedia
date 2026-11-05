-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_needTop_le_kme
-- name    : GeneralPieces.TopDisplay.needTop_le_kme
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:27.399324+00:00
-- url     : https://prove2.me/theorems/41d3aeb8-9d71-46cd-b3df-725829d673ea
-- title:
--   Top Display: need Top le kme
-- statement:
--   The same for the exponent of the algorithm of this development, at an index with m^{1/(9d)} ≤ K
--   ≤ m^{1/9}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L419-L426
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L419-L426

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

theorem GeneralPieces.TopDisplay.needTop_le_kme {Idx : Type} [Enc Idx] (S : Solver Idx) (i : Idx) (e : ℝ) (C₀ k m d : ℕ) (he1 : e ≤ 1)
    (hK : 2 ≤ S.K i) (hk : 1 ≤ k) (hd : 2 ≤ d) (hm : S.K i ^ 9 ≤ m) (hm' : m ≤ S.K i ^ (9 * d)) (he : 1 / Real.logb 2 (S.K i) ^ C₀ ≤ e)
    (hrate : ∀ lam B : ℕ, 1 ≤ lam → 1 ≤ B → (S.need (i, List.replicate lam (), List.replicate B ()) : ℝ) ≤
      e * (S.K i : ℝ) ^ 2 * lam + C₀ * (S.K i : ℝ) ^ 2 * Real.logb 2 (S.K i * (lam + B))) :
    (needTop S i k m : ℝ) ≤ (Atop C₀ d : ℕ) * k * m * e := by sorry
