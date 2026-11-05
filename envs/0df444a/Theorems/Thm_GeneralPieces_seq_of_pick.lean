-- Prove2me | Theorems.Thm_GeneralPieces_seq_of_pick
-- name    : GeneralPieces.seq_of_pick
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:46:15.806351+00:00
-- url     : https://prove2.me/theorems/66eda538-a3f3-4cda-b683-793375dfb9b1
-- title:
--   General Pieces: seq of pick
-- statement:
--   The theorem on the general recursion, parts (a) and (b), in the form that the top levels use,
--   with a given program that picks the level. The constant is C₀ + 10 for the C₀ of part (b): the
--   fields `K_le` (K_{ℓ+1} ≤ K_ℓ^10) and `e_ge` want
--   it to be at least 10 and at least 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean#L51-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean#L51-L104

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

theorem GeneralPieces.seq_of_pick (hCh : StChain2) (hR : StRate2) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) (P : PiecesF) (ρ : ℝ) (c x₀ : ℕ)
    (hρ : 1 / 2 ≤ ρ) (hρ1 : ρ < 1) (hP : Par P ρ c) (hm : P.m = 1) (hx : 18 ≤ x₀) (hx2 : c + 5 ≤ 2 ^ x₀) (pick : U → U × (List Step × U)) (hp1 : PolyT pick)
    (hp2 : ∀ b, (pick b).2 = idx P x₀ (pick b).1.length) (hp3 : ∀ b, K x₀ 0 ≤ b.length → K x₀ (pick b).1.length ≤ b.length)
    (hp4 : ∀ b, b.length < K x₀ ((pick b).1.length + 1)) :
    ∃ C₀ : ℕ, ∃ Q : (solverOf P).Seq (e ρ x₀) C₀, (∀ l, Q.idx l = idx P x₀ l) ∧ Q.pick = pick := by sorry
