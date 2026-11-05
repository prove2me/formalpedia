-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_three
-- name    : GeneralPieces.GenF.pderiv_three
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:15.566326+00:00
-- url     : https://prove2.me/theorems/3ddf0cd9-4edb-4019-bcba-24f809f3d857
-- title:
--   Gen F: pderiv three
-- statement:
--   ∂/∂x_i of e^a·e^b·c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L90-L95
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L90-L95

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

theorem GeneralPieces.GenF.pderiv_three (i : Y) {a b : MvPowerSeries Y A} (ha : MvPowerSeries.constantCoeff a = 0) (hb : MvPowerSeries.constantCoeff b = 0) (c : MvPowerSeries Y A) :
    MvPowerSeries.pderiv A i (expW a * (expW b * c)) =
      (MvPowerSeries.pderiv A i a + MvPowerSeries.pderiv A i b) * (expW a * (expW b * c)) + expW a * (expW b * MvPowerSeries.pderiv A i c) := by sorry
