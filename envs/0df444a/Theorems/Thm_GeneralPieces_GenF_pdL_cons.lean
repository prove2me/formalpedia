-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pdL_cons
-- name    : GeneralPieces.GenF.pdL_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:27:07.957207+00:00
-- url     : https://prove2.me/theorems/9790c446-b581-47ad-9e23-4844731f6490
-- title:
--   Gen F: pd L cons
-- statement:
--   The Gen F construction uses the pd L cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L42-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L42-L42

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

theorem GeneralPieces.GenF.pdL_cons (i : Y) (L : List Y) (F : MvPowerSeries Y R) : pdL (i :: L) F = pdL L (pderiv R i F) := by sorry
