-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_pderiv_rat_smul
-- name    : GeneralPieces.GenF.Y.pderiv_rat_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:00.804709+00:00
-- url     : https://prove2.me/theorems/715c4814-0626-4bcb-b9ef-dbbb95f53746
-- title:
--   Y: pderiv rat smul
-- statement:
--   The Y construction uses the pderiv rat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L104-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L104-L104

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

theorem GeneralPieces.GenF.Y.pderiv_rat_smul (i : Z) (q : ℚ) (F : MvPowerSeries Z R) : pderiv R i (q • F) = q • pderiv R i F := by sorry
