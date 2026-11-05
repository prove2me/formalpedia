-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Normal_pderiv_rat_smul
-- name    : GeneralPieces.GenF.Normal.pderiv_rat_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:08.155819+00:00
-- url     : https://prove2.me/theorems/0ebd8e11-0da5-48ab-95e1-2834e7f7b7e6
-- title:
--   Normal: pderiv rat smul
-- statement:
--   The Normal construction uses the pderiv rat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L67-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L67-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {Y A : Type} [CommRing A] [Algebra ℚ A]

theorem GeneralPieces.GenF.Normal.pderiv_rat_smul (i : Y) (q : ℚ) (f : MvPowerSeries Y A) : MvPowerSeries.pderiv A i (q • f) = q • MvPowerSeries.pderiv A i f := by sorry
