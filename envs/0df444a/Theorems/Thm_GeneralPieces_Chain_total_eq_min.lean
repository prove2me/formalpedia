-- Prove2me | Theorems.Thm_GeneralPieces_Chain_total_eq_min
-- name    : GeneralPieces.Chain.total_eq_min
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:45:50.626196+00:00
-- url     : https://prove2.me/theorems/0692ce16-4982-43d5-8853-4466bfb11236
-- title:
--   Chain: total eq min
-- statement:
--   The network that the program takes on a square grid is "the network with the smaller total": its
--   total is min(U_row, U_col).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L40-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L40-L45

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

theorem GeneralPieces.Chain.total_eq_min (P : PiecesF) (a h lam y : ℕ) :
    totalG P a a (decide (totalG P a a true h lam y < totalG P a a false h lam y)) h lam y =
      min (totalG P a a false h lam y) (totalG P a a true h lam y) := by sorry
