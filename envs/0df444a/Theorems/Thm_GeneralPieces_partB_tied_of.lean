-- Prove2me | Theorems.Thm_GeneralPieces_partB_tied_of
-- name    : GeneralPieces.partB_tied_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:56.142201+00:00
-- url     : https://prove2.me/theorems/e339c8a8-dff9-437a-bdd2-0bc808a6429c
-- title:
--   General Pieces: part B tied of
-- statement:
--   Part (b) for the named program, from the interface statements; C₀ depends on c only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/PartB.lean#L84-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/PartB.lean#L84-L97

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_Defs
import Definitions.Def_GeneralPieces_Rec_Seq
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Rec_Descend
import Definitions.Def_GeneralPieces_Rec_Level
import Definitions.Def_ClauseBound_Gen_Pick
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_ClauseBound_Alg_Need
import Definitions.Def_ClauseBound_Alg_Enum
import Definitions.Def_ClauseBound_Alg_Grid
import Definitions.Def_ClauseBound_Alg_CertEnum
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_Alg_CertLevel
import Definitions.Def_PaddedDescent_Col_CertG
import Definitions.Def_GeneralPieces_Rec_PartB
set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen Levels.Gen

theorem GeneralPieces.partB_tied_of (hR : StRate2) (hCh : StChain2) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) (hCS : ∀ P, StCertSolveG P) (c : ℕ) :
    ∃ C₀ : ℕ, ∀ (P : PiecesF) (ρ : ℝ) (x₀ : ℕ), 1 / 2 ≤ ρ → ρ < 1 → Par P ρ c → P.m = 1 → P.Keeps → 18 ≤ x₀ → c + 5 ≤ 2 ^ x₀ → Tied.PartB P ρ x₀ C₀ := by sorry
