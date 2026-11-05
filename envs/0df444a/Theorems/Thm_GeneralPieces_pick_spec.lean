-- Prove2me | Theorems.Thm_GeneralPieces_pick_spec
-- name    : GeneralPieces.pick_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:03:32.542874+00:00
-- url     : https://prove2.me/theorems/bc37f966-b117-4d3c-9d5a-4c9d87bfbf9b
-- title:
--   General Pieces: pick spec
-- statement:
--   What the program `ClauseBound.Gen.Pick.pick` does: from a bound in unary, in polynomial time,
--   the largest ℓ with K_ℓ ≤ bound (ℓ = 0 if the bound is below K₀) and the schedule of display (40) for
--   that ℓ. This is `ClauseBound.Gen.Pick.stPick` with the program named.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean#L33-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean#L33-L45

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Rate
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_GeneralPieces_Rec_Seq
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.all
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen

theorem GeneralPieces.pick_spec (P : PiecesF) (x₀ : ℕ) : PolyT (Pick.pick P x₀) ∧ (∀ b, (Pick.pick P x₀ b).2 = idx P x₀ (Pick.pick P x₀ b).1.length) ∧
    (∀ b, K x₀ 0 ≤ b.length → K x₀ (Pick.pick P x₀ b).1.length ≤ b.length) ∧ ∀ b, b.length < K x₀ ((Pick.pick P x₀ b).1.length + 1) := by sorry
