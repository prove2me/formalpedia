-- Prove2me | Theorems.Thm_GeneralPieces_boundInM_tied
-- name    : GeneralPieces.boundInM_tied
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:43:24.877413+00:00
-- url     : https://prove2.me/theorems/59067f6c-6131-4def-8fbf-77f60f17f407
-- title:
--   General Pieces: bound In M tied
-- statement:
--   The bound in m for the named programs, from Theorem B (pieces with ρ = 1/√2) and part (c) of
--   Theorem A.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/Bound.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/Bound.lean#L35-L37

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

theorem GeneralPieces.boundInM_tied (hB : AppRunningTime.ThmHalfPieces) : Tied.BoundInM := by sorry
