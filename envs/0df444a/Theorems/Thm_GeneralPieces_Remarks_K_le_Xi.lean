-- Prove2me | Theorems.Thm_GeneralPieces_Remarks_K_le_Xi
-- name    : GeneralPieces.Remarks.K_le_Xi
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:00:38.755193+00:00
-- url     : https://prove2.me/theorems/9687bd27-6a66-4339-9f41-4763b75a9808
-- title:
--   Remarks: K le Xi
-- statement:
--   K_ℓ ≤ Ξ = g²(λ + B).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L33-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L33-L38

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

theorem GeneralPieces.Remarks.K_le_Xi (x₀ l lam B : ℕ) (hlam : 1 ≤ lam) : K x₀ l ≤ g x₀ l ^ 2 * (lam + B) := by sorry
