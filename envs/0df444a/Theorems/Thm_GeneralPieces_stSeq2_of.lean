-- Prove2me | Theorems.Thm_GeneralPieces_stSeq2_of
-- name    : GeneralPieces.stSeq2_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:28:47.832402+00:00
-- url     : https://prove2.me/theorems/4dbfb985-200d-4dec-9445-321a740e3872
-- title:
--   General Pieces: st Seq2 of
-- statement:
--   The same from the five interface statements.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean#L107-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Seq.lean#L107-L111

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

theorem GeneralPieces.stSeq2_of (hCh : StChain2) (hR : StRate2) (hPk : StPick) (hSolve : ∀ P, StSolveG2 P) (hNeed : ∀ P, StNeedG P) : StSeq2 := by sorry
