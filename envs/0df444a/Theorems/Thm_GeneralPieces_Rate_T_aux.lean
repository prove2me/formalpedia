-- Prove2me | Theorems.Thm_GeneralPieces_Rate_T_aux
-- name    : GeneralPieces.Rate.T_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:35.145219+00:00
-- url     : https://prove2.me/theorems/896232b5-619e-4711-ac40-dad71571a6f1
-- title:
--   Rate: T aux
-- statement:
--   The display for 𝒯 in real variables: k2 = K², G4 = g⁴, L = log Ξ, lg = log(K(L + B')).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L318-L325
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L318-L325

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

theorem GeneralPieces.Rate.T_aux (e0 r N k2 G4 L c lam' lg C : ℝ) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1)
    (H3 : k2 * lam' ≤ r * N + c / 4 * G4 * L + k2) (H4 : lg ≤ (c + 5) * L) (hL : 1 ≤ L) (hk2 : 0 ≤ k2) (hG : 0 ≤ G4) (hc : 0 ≤ c) (hC : 0 ≤ C) :
    e0 * k2 * lam' + C * k2 * lg ≤ e0 * r * N + (c / 4 * G4 + k2 + (c + 5) * C * k2) * L := by sorry
