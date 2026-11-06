-- Prove2me | Theorems.Thm_GeneralPieces_Remarks_card_term_le
-- name    : GeneralPieces.Remarks.card_term_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:00:19.824181+00:00
-- url     : https://prove2.me/theorems/ec06b45a-f213-4417-baef-0fc1c4722071
-- title:
--   Remarks: card term le
-- statement:
--   «(2|𝓘| + 2)·2^{cλ} ≤ Ξ^{c+1}·τ», where |𝓘| ≤ (2λ)^c, τ = 2^{cλ}·Ξ^{C₂} and Ξ = g²(λ + B) with g
--   ≥ 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L46-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Remarks.lean#L46-L60

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

theorem GeneralPieces.Remarks.card_term_le (a c lam B I C₂ : ℕ) (ha : 2 ≤ a) (hlam : 1 ≤ lam) (hI : I ≤ (2 * lam) ^ c) :
    (2 * I + 2) * 2 ^ (c * lam) ≤ (a ^ 2 * (lam + B)) ^ (c + 1) * (2 ^ (c * lam) * (a ^ 2 * (lam + B)) ^ C₂) := by sorry
