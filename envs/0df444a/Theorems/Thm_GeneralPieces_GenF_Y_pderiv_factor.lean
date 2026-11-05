-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_pderiv_factor
-- name    : GeneralPieces.GenF.Y.pderiv_factor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:44.044189+00:00
-- url     : https://prove2.me/theorems/3e8a655a-2562-480f-8576-ff615fb4181a
-- title:
--   Y: pderiv factor
-- statement:
--   The Y construction uses the pderiv factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L137-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L137-L139

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

theorem GeneralPieces.GenF.Y.pderiv_factor (rd : Bool) (i : X) (k : ℕ) : pderiv Tv i (C (tT k) + (k : ℚ) • embW (sfB' rd k)) = C (emb ((k : ℚ) • cB rd k i)) := by sorry
