-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_emb_rat_smul
-- name    : GeneralPieces.GenF.Y.emb_rat_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:21.246506+00:00
-- url     : https://prove2.me/theorems/1173b2f0-8fb4-4bd8-8480-57a11e192cde
-- title:
--   Y: emb rat smul
-- statement:
--   The Y construction uses the emb rat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L129-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L129-L131

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

theorem GeneralPieces.GenF.Y.emb_rat_smul (q : ℚ) (s : S) : emb (q • s) = q • emb s := by sorry
