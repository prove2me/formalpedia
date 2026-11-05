-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_top_arith
-- name    : GeneralPieces.TopDisplay.top_arith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:27.083788+00:00
-- url     : https://prove2.me/theorems/8b566838-c6d0-4a76-bae0-4b4023b4068c
-- title:
--   Top Display: top arith
-- statement:
--   Part (c) as an inequality for the schedule of the theorem, from `top_level`: with ℓ the level
--   picked for m ≥ K₀⁹, the exponent, at most 2·e_ℓ·k·m + O(k·m^{1−1/90}), is at most
--   `Atop C₀ 10`·k·m·e_ℓ. This is what the top level in m is given for the schedule;
--   `stTopArith2` is the same for a general sequence of levels.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L503-L513
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L503-L513

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_StepMachines_Prog_CountNet
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_GeneralPieces_Num_TopDisplay
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.TopDisplay
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.Gen Levels.Gen GeneralPieces.PartA

theorem GeneralPieces.TopDisplay.top_arith (P : PiecesF) (ρ : ℝ) (x₀ C₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (Q : (solverOf P).Seq (e ρ x₀) C₀)
    (hQ : ∀ l, Q.idx l = idx P x₀ l) (k m : ℕ) (hk : 1 ≤ k) (hm : K x₀ 0 ^ 9 ≤ m) :
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ (Atop C₀ 10 : ℕ) * k * m * e ρ x₀ (Q.pick (root9 m)).1.length := by sorry
