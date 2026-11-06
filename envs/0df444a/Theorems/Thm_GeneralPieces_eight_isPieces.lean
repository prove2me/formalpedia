-- Prove2me | Theorems.Thm_GeneralPieces_eight_isPieces
-- name    : GeneralPieces.eight_isPieces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:08:30.020381+00:00
-- url     : https://prove2.me/theorems/9f85f25b-afc2-4eac-9164-d70ff2a1ff93
-- title:
--   General Pieces: eight is Pieces
-- statement:
--   The functions A_0, …, A_t of Lemma 2, with their programs, are pieces with parameters (11/12, c)
--   for every c ≥ 8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesFromEightSquares/LemPieces.lean#L33-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/PiecesFromEightSquares/LemPieces.lean#L33-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesFromEightSquaresStatement
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_ClauseBoundStatement
import Definitions.Def_Eight_SecCrossing_LemPieces
import Definitions.Def_ClauseBound_Gen_Defs
import Definitions.Def_Eight_App_Pieces
import Definitions.Def_Eight_App_Rate
import Definitions.Def_PiecesFromEightSquares_LemPieces
set_option autoImplicit false
section
section
open GeneralPieces
open Finset Groundwork PaddedDescent.F ClauseBound.Alg AppRunningTime Eight

theorem GeneralPieces.eight_isPieces {c : ℕ} (hc : 8 ≤ c) : IsPieces (11 / 12) c eightF Eight.A valEight := by sorry
