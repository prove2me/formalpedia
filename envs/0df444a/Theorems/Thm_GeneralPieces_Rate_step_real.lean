-- Prove2me | Theorems.Thm_GeneralPieces_Rate_step_real
-- name    : GeneralPieces.Rate.step_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:04.215401+00:00
-- url     : https://prove2.me/theorems/8df06fbb-be32-4f35-b152-a0b1402ee08a
-- title:
--   Rate: step real
-- statement:
--   All budgets of a step but the first, in real variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L423-L452
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L423-L452

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

theorem GeneralPieces.Rate.step_real (nd sz' sc' sP lg L vt vs vg lam' sc sz vn e' e0 r k G4 lm cc : ℝ)
    (hIH : nd ≤ sc' + sz' + (e0 * k ^ 2 * lam' + (6 * cc + 14) * k ^ 2 * lg))
    (H1 : sc' ≤ sc + (cc * G4 * L + 1)) (HP : sP ≤ cc * G4 * L + 1) (H2 : sz' ≤ sz + 1 + ((cc + 3) * L + 1))
    (H3 : k ^ 2 * lam' ≤ r * (G4 * lm) + cc / 4 * G4 * L + k ^ 2) (H4 : lg ≤ (cc + 5) * L) (H5 : 2 * ((cc + 5) * k ^ 2) ≤ G4)
    (hk1 : 1 ≤ k) (hkG : k ≤ G4) (hc0 : 0 ≤ cc) (hlm : 1 ≤ lm) (hL1 : 1 ≤ L) (h3 : 3 ≤ e' * k)
    (he0 : 0 ≤ e0) (he1 : e0 ≤ 1) (he'0 : 0 ≤ e') (hre : r * e0 ≤ e') (hr2 : r ≤ 2) (hneed : k * vn ≤ G4 * lm) (hgK : vg ≤ G4)
    (hst : k * vs ≤ 3 * (G4 * lm)) (htab : vt ≤ k * lam') (p1 : 0 ≤ sc) (p2 : 0 ≤ sz) :
    max (max (max vn sP) (max vg vs)) (max (max vt 0) nd) ≤ sc + sz + (e' * (G4 * lm) + (6 * cc + 14) * G4 * L) := by sorry
