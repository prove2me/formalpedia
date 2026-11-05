-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_top_level
-- name    : GeneralPieces.TopDisplay.top_level
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:35:08.99922+00:00
-- url     : https://prove2.me/theorems/a1858381-f60a-46a8-9109-b9a5a00711ab
-- title:
--   Top Display: top level
-- statement:
--   The proof of part (c) up to its display, for the algorithm of this development with the schedule
--   K_ℓ, e_ℓ and any x₀ ≥ 18. Given parts (a) and (b) in the form of a sequence of indices Q, and m ≥
--   K₀⁹, let ℓ be
--   the level that the algorithm picks for m. Then K_ℓ ≤ m^{1/9} < K_{ℓ+1} (it is the largest such ℓ),
--   K_ℓ ≥ m^{1/90}, the exponent is at most
--   2·e_ℓ·k·m + A·(km/K_ℓ + K_ℓ⁸·log K_ℓ + K_ℓ²·log(km)), and at most 2·e_ℓ·k·m + 203·A·k·m^{1−1/90},
--   where A = 2C₀ + 15.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L463-L497
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L463-L497

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

theorem GeneralPieces.TopDisplay.top_level (P : PiecesF) (ρ : ℝ) (x₀ C₀ : ℕ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (Q : (solverOf P).Seq (e ρ x₀) C₀)
    (hQ : ∀ l, Q.idx l = idx P x₀ l) (k m : ℕ) (hk : 1 ≤ k) (hm : K x₀ 0 ^ 9 ≤ m) :
    K x₀ (Q.pick (root9 m)).1.length ^ 9 ≤ m ∧ m < K x₀ ((Q.pick (root9 m)).1.length + 1) ^ 9 ∧
    (m : ℝ) ^ (1 / 90 : ℝ) ≤ K x₀ (Q.pick (root9 m)).1.length ∧
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ 2 * e ρ x₀ (Q.pick (root9 m)).1.length * k * m + (2 * C₀ + 15 : ℕ) *
      ((k : ℝ) * m / K x₀ (Q.pick (root9 m)).1.length +
        (K x₀ (Q.pick (root9 m)).1.length : ℝ) ^ 8 * Real.logb 2 (K x₀ (Q.pick (root9 m)).1.length) +
        (K x₀ (Q.pick (root9 m)).1.length : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) * m)) ∧
    (needTop (solverOf P) (Q.pick (root9 m)).2 k m : ℝ) ≤ 2 * e ρ x₀ (Q.pick (root9 m)).1.length * k * m +
      (203 * (2 * C₀ + 15) : ℕ) * (k * (m : ℝ) ^ (1 - 1 / 90 : ℝ)) := by sorry
