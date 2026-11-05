-- Prove2me | Theorems.Thm_GeneralPieces_Rate_tab_aux
-- name    : GeneralPieces.Rate.tab_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:40.160916+00:00
-- url     : https://prove2.me/theorems/bf85509b-eba8-4068-ae71-76dbed0c42e9
-- title:
--   Rate: tab aux
-- statement:
--   The budget (K − 1)·L of a table one level down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L376-L387
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L376-L387

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

theorem GeneralPieces.Rate.tab_aux (k v r N c G4 L e' : ℝ) (hk : 1 ≤ k) (hv : k * v ≤ r * N + c / 4 * G4 * L + k ^ 2) (hr : r ≤ 2) (hc : 0 ≤ c)
    (h3 : 3 ≤ e' * k) (hN : 0 ≤ N) (hkG : k ≤ G4) (hL : 1 ≤ L) : v ≤ e' * N + (6 * c + 14) * G4 * L := by sorry
