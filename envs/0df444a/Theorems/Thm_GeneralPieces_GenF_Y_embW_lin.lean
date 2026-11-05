-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_embW_lin
-- name    : GeneralPieces.GenF.Y.embW_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:41.969344+00:00
-- url     : https://prove2.me/theorems/887897ec-824d-48ac-aea8-76b99049ff26
-- title:
--   Y: emb W lin
-- statement:
--   The Y construction uses the emb W lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L133-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L133-L135

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
open GeneralPieces.GenF.Y

theorem GeneralPieces.GenF.Y.embW_lin (c : X → S) : embW (lin c) = lin fun i => emb (c i) := by sorry
