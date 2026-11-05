-- Prove2me | Theorems.Thm_GeneralPieces_Level_stExpandG2
-- name    : GeneralPieces.Level.stExpandG2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:29:47.242191+00:00
-- url     : https://prove2.me/theorems/929bd9bc-1ac0-4ee0-932d-b9b994165ebd
-- title:
--   Level: st Expand G2
-- statement:
--   One level: the factor d^|R| times Z is the sum of the terms evaluated at once and of the values
--   of the new instances; these are well formed; there are few; the sum is small.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L137-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Level.lean#L137-L197

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Group_Lemma
import Definitions.Def_ClauseBound_Alg_Level
import Definitions.Def_GeneralPieces_Rec_Level
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Level
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.Level Finset

theorem GeneralPieces.Level.stExpandG2 (P : PiecesF) (hG : StGrid P) (hE : StEnum) : StExpandG2 P := by sorry
