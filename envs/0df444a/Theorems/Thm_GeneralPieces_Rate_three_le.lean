-- Prove2me | Theorems.Thm_GeneralPieces_Rate_three_le
-- name    : GeneralPieces.Rate.three_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:54.29006+00:00
-- url     : https://prove2.me/theorems/e37488f9-7560-4130-8037-5e4e3c8511d9
-- title:
--   Rate: three le
-- statement:
--   3 ≤ e_{ℓ+1}·K_ℓ: the term 3/K_ℓ of e_{ℓ+1} pays for 2^{2N/K + cλ} in the paper; here each of the
--   budgets of size N/K fits under e_{ℓ+1}·N by itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L347-L352
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L347-L352

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

theorem GeneralPieces.Rate.three_le (hA : PartA.TheoremAa ρ x₀) (hρ : 0 ≤ ρ) (l : ℕ) : 3 ≤ e ρ x₀ (l + 1) * K x₀ l := by sorry
