-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_inv_logK_le_e
-- name    : GeneralPieces.PartAUse.inv_logK_le_e
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:06.680079+00:00
-- url     : https://prove2.me/theorems/de46e8f1-5088-47f1-8634-d80dfd50a1b2
-- title:
--   Part AUse: inv log K le e
-- statement:
--   «… 2^{−ℓ−1} ≥ 1/log K_ℓ», so e_ℓ ≥ 1/log K_ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L80-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L80-L81

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Alg_TopArith
import Definitions.Def_GeneralPieces_Num_PartAUse
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.PartAUse
open Levels.Gen ClauseBound.Gen ClauseBound.Alg ClauseBound.Alg.TopArith GeneralPieces.PartA
variable {ρ : ℝ} {x₀ : ℕ}

theorem GeneralPieces.PartAUse.inv_logK_le_e (hA : TheoremAa ρ x₀) (hρ : 1 / 2 ≤ ρ) (hx : 2 ≤ x₀) (l : ℕ) : 1 / Real.logb 2 (K x₀ l) ≤ e ρ x₀ l := by sorry
