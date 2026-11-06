-- Prove2me | Theorems.Thm_GeneralPieces_runB_polyT
-- name    : GeneralPieces.runB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:30:03.351529+00:00
-- url     : https://prove2.me/theorems/ce6e34f4-492b-4e6f-8af7-88318171005f
-- title:
--   General Pieces: run B poly T
-- statement:
--   The named program is polynomial-time in (pad, ℓ, instance), if the descent through all levels
--   is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/PartB.lean#L68-L81
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/PartB.lean#L68-L81

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

theorem GeneralPieces.runB_polyT (P : PiecesF) (x₀ : ℕ) (hCS : StCertSolveG P) (hKeeps : P.Keeps) : PolyT (Tied.runB P x₀) := by sorry
