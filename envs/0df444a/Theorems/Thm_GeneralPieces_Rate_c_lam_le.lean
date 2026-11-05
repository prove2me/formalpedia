-- Prove2me | Theorems.Thm_GeneralPieces_Rate_c_lam_le
-- name    : GeneralPieces.Rate.c_lam_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:41:13.559888+00:00
-- url     : https://prove2.me/theorems/387c295d-3b7a-4708-83a9-a45e932bfe6a
-- title:
--   Rate: c lam le
-- statement:
--   "cλ ≤ N/K".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L334-L343
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L334-L343

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}

theorem GeneralPieces.Rate.c_lam_le (hx : 18 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (l lam : ℕ) : K x₀ l * (c * lam) ≤ g x₀ l ^ 4 * lam := by sorry
