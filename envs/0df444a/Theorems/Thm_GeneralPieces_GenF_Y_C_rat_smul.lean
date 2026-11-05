-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_C_rat_smul
-- name    : GeneralPieces.GenF.Y.C_rat_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:23.488707+00:00
-- url     : https://prove2.me/theorems/341ed6f4-01b7-4c2b-8078-6c4c56a0775d
-- title:
--   Y: C rat smul
-- statement:
--   The Y construction uses the C rat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L106-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L106-L106

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
open GeneralPieces.GenF.Y
variable {Z R : Type} [CommRing R] [Algebra ℚ R]

theorem GeneralPieces.GenF.Y.C_rat_smul (q : ℚ) (r : R) : (C (q • r) : MvPowerSeries Z R) = q • C r := by sorry
