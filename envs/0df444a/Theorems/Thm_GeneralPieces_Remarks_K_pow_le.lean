-- Prove2me | Theorems.Thm_GeneralPieces_Remarks_K_pow_le
-- name    : GeneralPieces.Remarks.K_pow_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:00:38.034649+00:00
-- url     : https://prove2.me/theorems/12a487bd-96bc-4830-895b-cdb56c8a8dd0
-- title:
--   Remarks: K pow le
-- statement:
--   «K^g ≤ Ξ^g».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L41-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L41-L42

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_AppRunningTimeStatement
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_GeneralPieces_Num_Remarks
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Remarks
open Finset Levels.Gen ClauseBound.Gen AppRunningTime

theorem GeneralPieces.Remarks.K_pow_le (x₀ l lam B : ℕ) (hlam : 1 ≤ lam) : K x₀ l ^ g x₀ l ≤ (g x₀ l ^ 2 * (lam + B)) ^ g x₀ l := by sorry
