-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Normal_mapD_C
-- name    : GeneralPieces.GenF.Normal.mapD_C
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:55.49326+00:00
-- url     : https://prove2.me/theorems/a810f242-ff2e-431e-9899-9d9bbd660007
-- title:
--   Normal: map D C
-- statement:
--   The Normal construction uses the map D C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L59-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L59-L65

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

theorem GeneralPieces.GenF.Normal.mapD_C (d : Derivation ℚ A A) (a : A) : mapD (X := Y) d (MvPowerSeries.C a) = MvPowerSeries.C (d a) := by sorry
