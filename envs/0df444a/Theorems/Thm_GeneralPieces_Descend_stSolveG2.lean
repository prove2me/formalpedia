-- Prove2me | Theorems.Thm_GeneralPieces_Descend_stSolveG2
-- name    : GeneralPieces.Descend.stSolveG2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:12.852969+00:00
-- url     : https://prove2.me/theorems/e2fa2e82-6b17-41f7-a1f6-72b709942362
-- title:
--   Descend: st Solve G2
-- statement:
--   `StSolveG2`: all levels, brute force at the bottom and one division compute the sum Z of the
--   instance at the top.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Descend.lean#L107-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Descend.lean#L107-L117

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Defs
import Definitions.Def_ClauseBound_Alg_Descend
import Definitions.Def_GeneralPieces_Rec_Descend
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Descend
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Lists ClauseBound.Alg ClauseBound.Alg.Descend

theorem GeneralPieces.Descend.stSolveG2 (P : PiecesF) (hX : StExpandG2 P) : StSolveG2 P := by sorry
