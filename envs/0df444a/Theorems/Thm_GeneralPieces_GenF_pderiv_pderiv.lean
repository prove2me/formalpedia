-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_pderiv
-- name    : GeneralPieces.GenF.pderiv_pderiv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:09:10.081773+00:00
-- url     : https://prove2.me/theorems/41a5bba1-4e4f-446a-b085-e478143d8c55
-- title:
--   Gen F: pderiv pderiv
-- statement:
--   Two derivatives commute.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L74-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L74-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Borel
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open Finset MvPowerSeries
variable {Y R : Type} [CommRing R]

theorem GeneralPieces.GenF.pderiv_pderiv (i j : Y) (F : MvPowerSeries Y R) : pderiv R i (pderiv R j F) = pderiv R j (pderiv R i F) := by sorry
