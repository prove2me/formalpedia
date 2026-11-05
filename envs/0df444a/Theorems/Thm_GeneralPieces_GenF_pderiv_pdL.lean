-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_pdL
-- name    : GeneralPieces.GenF.pderiv_pdL
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:09:12.440336+00:00
-- url     : https://prove2.me/theorems/228d53e1-b9d2-4355-b5ae-7234ed0c1033
-- title:
--   Gen F: pderiv pd L
-- statement:
--   The Gen F construction uses the pderiv pd L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L82-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L82-L85

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

theorem GeneralPieces.GenF.pderiv_pdL (i : Y) (L : List Y) (F : MvPowerSeries Y R) : pderiv R i (pdL L F) = pdL L (pderiv R i F) := by sorry
