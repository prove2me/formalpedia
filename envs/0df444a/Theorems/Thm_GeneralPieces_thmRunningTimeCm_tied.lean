-- Prove2me | Theorems.Thm_GeneralPieces_thmRunningTimeCm_tied
-- name    : GeneralPieces.thmRunningTimeCm_tied
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:44:28.0566+00:00
-- url     : https://prove2.me/theorems/f21007ee-1ab7-4505-9d9f-e007ac016332
-- title:
--   General Pieces: thm Running Time Cm tied
-- statement:
--   Part (c) of Theorem A, first sentence, for the named programs, for every x₀ of the theorem.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/Bound.lean#L28-L28
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Tied/Bound.lean#L28-L28

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

theorem GeneralPieces.thmRunningTimeCm_tied : Tied.ThmRunningTimeCm := by sorry
