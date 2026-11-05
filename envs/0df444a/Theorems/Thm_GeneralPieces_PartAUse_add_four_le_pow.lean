-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_add_four_le_pow
-- name    : GeneralPieces.PartAUse.add_four_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:27:00.253849+00:00
-- url     : https://prove2.me/theorems/4a74024c-fc26-4bfe-ad70-1c15b7153290
-- title:
--   Part AUse: add four le pow
-- statement:
--   If n < K_{ℓ+1}^17 then n + 4 ≤ K_ℓ^171, by K_{ℓ+1} ≤ K_ℓ^10.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L202-L209
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L202-L209

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

theorem GeneralPieces.PartAUse.add_four_le_pow (hA : TheoremAa ρ x₀) {l n : ℕ} (hlt : n < K x₀ (l + 1) ^ 17) : n + 4 ≤ K x₀ l ^ 171 := by sorry
