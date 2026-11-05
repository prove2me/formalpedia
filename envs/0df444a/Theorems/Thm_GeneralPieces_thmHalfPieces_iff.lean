-- Prove2me | Theorems.Thm_GeneralPieces_thmHalfPieces_iff
-- name    : GeneralPieces.thmHalfPieces_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:52:53.65764+00:00
-- url     : https://prove2.me/theorems/70aca08b-d4d2-4a09-a351-a70450860a8a
-- title:
--   General Pieces: thm Half Pieces iff
-- statement:
--   Theorem B (pieces with ρ = 1/√2) says that some programs are the pieces of Appendix B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/Bound.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/Bound.lean#L31-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Tied_BoundDefs
import Definitions.Def_GeneralPieces_ThmRunningTime
import Definitions.Def_GeneralPieces_Num_Asymptotic
import Definitions.Def_GeneralPieces_Half_Main
import Definitions.Def_GeneralPieces_Tied_Bound
set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Inst.Rec ClauseBound.Inst.Half GeneralPieces.Half

theorem GeneralPieces.thmHalfPieces_iff : AppRunningTime.ThmHalfPieces ↔ ∃ c P A val, Tied.IsPiecesB c P A val := by sorry
