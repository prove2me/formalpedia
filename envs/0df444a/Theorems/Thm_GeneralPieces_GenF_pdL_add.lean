-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pdL_add
-- name    : GeneralPieces.GenF.pdL_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:27:17.853197+00:00
-- url     : https://prove2.me/theorems/18fcac5c-1f10-4b6f-b4ee-0de6d5b8a1b0
-- title:
--   Gen F: pd L add
-- statement:
--   The Gen F construction uses the pd L add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L49-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L49-L52

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

theorem GeneralPieces.GenF.pdL_add (L : List Y) (F G : MvPowerSeries Y R) : pdL L (F + G) = pdL L F + pdL L G := by sorry
