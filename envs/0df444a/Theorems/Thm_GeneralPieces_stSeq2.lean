-- Prove2me | Theorems.Thm_GeneralPieces_stSeq2
-- name    : GeneralPieces.stSeq2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:31.175886+00:00
-- url     : https://prove2.me/theorems/bb1f6b34-ccac-415d-8e76-13140fff4500
-- title:
--   General Pieces: st Seq2
-- statement:
--   The same from the two statements that are proved elsewhere: every step of the schedule is in
--   order, and all levels together give the value of the clique.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean#L115-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean#L115-L116

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
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Seq Levels.Gen

theorem GeneralPieces.stSeq2 (hChain : StChain2) (hSolve : ∀ P, StSolveG2 P) : StSeq2 := by sorry
