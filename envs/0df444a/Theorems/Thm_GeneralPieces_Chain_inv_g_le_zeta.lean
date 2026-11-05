-- Prove2me | Theorems.Thm_GeneralPieces_Chain_inv_g_le_zeta
-- name    : GeneralPieces.Chain.inv_g_le_zeta
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:38:52.572594+00:00
-- url     : https://prove2.me/theorems/0e93cf4b-6933-4477-94f2-bccafd34ec37
-- title:
--   Chain: inv g le zeta
-- statement:
--   "Also 1/g ≤ ζ".
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L171-L179
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L171-L179

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_ClauseBound_Gen_Chain
import Definitions.Def_ClauseBound_Gen_Rate
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_GeneralPieces_Rec_Chain
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Chain
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c : ℕ}

theorem GeneralPieces.Chain.inv_g_le_zeta (x₀ l : ℕ) (hx : 18 ≤ x₀) : 1 / (g x₀ l : ℝ) ≤ zeta l := by sorry
