-- Prove2me | Theorems.Thm_GeneralPieces_stRate2
-- name    : GeneralPieces.stRate2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:02:41.46133+00:00
-- url     : https://prove2.me/theorems/e1318046-2050-4258-b3aa-0094fc994044
-- title:
--   General Pieces: st Rate2
-- statement:
--   Theorem A, part (b), for the exponent of the pad, for every x₀ ≥ 18 with 2^x₀ ≥ c + 5, with C₀ =
--   6c + 17.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L504-L520
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Rate.lean#L504-L520

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open GeneralPieces
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen

theorem GeneralPieces.stRate2 : StRate2 := by sorry
