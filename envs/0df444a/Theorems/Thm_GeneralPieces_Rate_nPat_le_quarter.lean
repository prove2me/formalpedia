-- Prove2me | Theorems.Thm_GeneralPieces_Rate_nPat_le_quarter
-- name    : GeneralPieces.Rate.nPat_le_quarter
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:36.084744+00:00
-- url     : https://prove2.me/theorems/7bdbc80c-4ceb-4868-8978-578ae697c0d0
-- title:
--   Rate: n Pat le quarter
-- statement:
--   "The |I|^{|R|} ≤ Ξ^{cg⁴/4} functions ι".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L127-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L127-L131

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

theorem GeneralPieces.Rate.nPat_le_quarter (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    nPat P (step P x₀ l) lam ≤ (g x₀ l ^ 2 * (lam + B)) ^ (c * (g x₀ l ^ 4 / 4)) := by sorry
