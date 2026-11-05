-- Prove2me | Theorems.Thm_GeneralPieces_Chain_ubar_eq
-- name    : GeneralPieces.Chain.ubar_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:38:39.693247+00:00
-- url     : https://prove2.me/theorems/8c1606db-eeef-47d4-a851-4c7820396895
-- title:
--   Chain: ubar eq
-- statement:
--   The program's upper bound for U at level ℓ, written out: g(g−1)·gλ + |R|·max_i (c_i^row +
--   c_i^col).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L49-L51
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L49-L51

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

theorem GeneralPieces.Chain.ubar_eq (P : PiecesF) (x₀ l lam : ℕ) :
    ubarG P (step P x₀ l) lam = g x₀ l * (g x₀ l - 1) * g x₀ l * lam + nRectG (g x₀ l) (g x₀ l) * capSum P 0 lam := by sorry
