-- Prove2me | Theorems.Thm_GeneralPieces_Rate_exponent_le
-- name    : GeneralPieces.Rate.exponent_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:10.542856+00:00
-- url     : https://prove2.me/theorems/7546d41f-d85c-4b9b-873f-4e903378ffe3
-- title:
--   Rate: exponent le
-- statement:
--   "The exponent of Ξ is at most (c + C₄ + 1)g⁴ + ½C₀g⁴ ≤ C₀g⁴ by the choice of C₀", together with
--   e(ρ + 3ζ) ≤ e_{ℓ+1}: the number of instances, the bit length of the sum so far and the
--   exponent one level down. Here k2 = K², G4 = g⁴, L = log Ξ, lg = log(K(L + B')).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L408-L420
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L408-L420

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

theorem GeneralPieces.Rate.exponent_le (e0 e' r N k2 G4 L c lam' lg : ℝ) (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (hre : r * e0 ≤ e') (hN : 0 ≤ N)
    (H3 : k2 * lam' ≤ r * N + c / 4 * G4 * L + k2) (H4 : lg ≤ (c + 5) * L) (H5 : 2 * ((c + 5) * k2) ≤ G4) (hL : 1 ≤ L)
    (hk2 : 0 ≤ k2) (hkG : k2 ≤ G4) (hG : 1 ≤ G4) (hc : 0 ≤ c) :
    (c * G4 * L + 1) + (1 + ((c + 3) * L + 1)) + (e0 * k2 * lam' + (6 * c + 14) * k2 * lg) ≤ e' * N + (6 * c + 14) * G4 * L := by sorry
