-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_lt_pow_ninety
-- name    : GeneralPieces.PartAUse.lt_pow_ninety
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:18.362937+00:00
-- url     : https://prove2.me/theorems/682eea8b-6f32-4b8e-8f6e-5a0b305ea084
-- title:
--   Part AUse: lt pow ninety
-- statement:
--   Proof of part (c), «by (a), K ≥ m^{1/90}»: if K_{ℓ+1} > m^{1/9} then m < K_ℓ^90, by K_{ℓ+1} ≤
--   K_ℓ^10.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L94-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L94-L97

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

theorem GeneralPieces.PartAUse.lt_pow_ninety (hA : TheoremAa ρ x₀) {l m : ℕ} (h : m < K x₀ (l + 1) ^ 9) : m < K x₀ l ^ 90 := by sorry
