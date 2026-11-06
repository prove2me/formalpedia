-- Prove2me | Theorems.Thm_GeneralPieces_thmHalfPieces
-- name    : GeneralPieces.thmHalfPieces
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:53:04.145172+00:00
-- url     : https://prove2.me/theorems/26a43c86-50be-4de1-a629-79b9709fe663
-- title:
--   General Pieces: thm Half Pieces
-- statement:
--   The theorem on pieces with ρ = 1/√2, with the running time, for the functions of its proof,
--   given the statements about the ring (`AppHalfPieces.PieceFacts`, proved in
--   `proof/rates/GeneralPieces/Main.lean`).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Main.lean#L40-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Main.lean#L40-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_Spec
import Definitions.Def_GeneralPieces_Half_Order
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Definitions.Def_ClauseBound_Inst_CertHalf
import Definitions.Def_ClauseBound_Inst_HalfEnd
import Definitions.Def_GeneralPieces_Half_Main
set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half

theorem GeneralPieces.thmHalfPieces (hPF : AppHalfPieces.PieceFacts) : AppRunningTime.ThmHalfPieces := by sorry
