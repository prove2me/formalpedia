-- Prove2me | Theorems.Thm_GeneralPieces_PartAUse_two_le_K
-- name    : GeneralPieces.PartAUse.two_le_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:51:43.48733+00:00
-- url     : https://prove2.me/theorems/4a4424a1-e0ab-487b-888d-2b003d46cc45
-- title:
--   Part AUse: two le K
-- statement:
--   K_ℓ ≥ 2, because K_ℓ < K_ℓ^10.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L37-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/PartAUse.lean#L37-L41

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

theorem GeneralPieces.PartAUse.two_le_K (hA : TheoremAa ρ x₀) (l : ℕ) : 2 ≤ K x₀ l := by sorry
