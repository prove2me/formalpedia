-- Prove2me | Theorems.Thm_GeneralPieces_Chain_zetaOf_step
-- name    : GeneralPieces.Chain.zetaOf_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:38:58.386401+00:00
-- url     : https://prove2.me/theorems/82e0a1b8-99c7-4ab5-ae3e-7590ae6ffce8
-- title:
--   Chain: zeta Of step
-- statement:
--   ζ of the step at level ℓ is ζ_ℓ = 2^{−ℓ−5}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L182-L185
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Chain.lean#L182-L185

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

theorem GeneralPieces.Chain.zetaOf_step (hm : P.m = 1) (x₀ l : ℕ) : zetaOf (step P x₀ l) = zeta l := by sorry
