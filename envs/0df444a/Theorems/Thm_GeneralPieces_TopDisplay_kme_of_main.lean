-- Prove2me | Theorems.Thm_GeneralPieces_TopDisplay_kme_of_main
-- name    : GeneralPieces.TopDisplay.kme_of_main
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:46:29.40022+00:00
-- url     : https://prove2.me/theorems/bc553779-ee0c-4678-a73c-60e083ecd318
-- title:
--   Top Display: kme of main
-- statement:
--   The end of the proof of the first sentence of part (c): an exponent X ≤ 2ekm + A'·k·m^{1−1/(9d)}
--   is O(k·m·e), because e ≥ (log K)^{−C₀}, K ≤ m^{1/9}, and m^{−1/(9d)} is smaller than any power of
--   1/log m, up to a
--   constant. (The text compares both terms with km/(log m)^{α'}; the top level of this development asks
--   for a multiple of k·m·e.)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L389-L415
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/TopDisplay.lean#L389-L415

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

theorem GeneralPieces.TopDisplay.kme_of_main (K C₀ k m d A' : ℕ) (e X : ℝ) (hK : 2 ≤ K) (hd : 1 ≤ d) (hm : K ^ 9 ≤ m) (he : 1 / Real.logb 2 K ^ C₀ ≤ e)
    (h : X ≤ 2 * e * k * m + (A' : ℝ) * (k * (m : ℝ) ^ (1 - 1 / (9 * d : ℝ)))) :
    X ≤ ((2 + A' * (d ^ C₀ * (C₀.factorial * 2 ^ C₀)) : ℕ) : ℝ) * k * m * e := by sorry
