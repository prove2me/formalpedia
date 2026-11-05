-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pdL_C_mul
-- name    : GeneralPieces.GenF.pdL_C_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:09:04.309975+00:00
-- url     : https://prove2.me/theorems/a7505491-7d97-4fb6-ade6-69679bd22d7f
-- title:
--   Gen F: pd L C mul
-- statement:
--   The Gen F construction uses the pd L C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L68-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L68-L71

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

theorem GeneralPieces.GenF.pdL_C_mul (L : List Y) (c : R) (F : MvPowerSeries Y R) : pdL L (C c * F) = C c * pdL L F := by sorry
