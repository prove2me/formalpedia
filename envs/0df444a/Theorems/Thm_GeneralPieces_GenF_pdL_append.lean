-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pdL_append
-- name    : GeneralPieces.GenF.pdL_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:09:00.482568+00:00
-- url     : https://prove2.me/theorems/82b92cf0-ffea-4afa-b565-b764602a8f25
-- title:
--   Gen F: pd L append
-- statement:
--   The Gen F construction uses the pd L append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L44-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L44-L47

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

theorem GeneralPieces.GenF.pdL_append (L L' : List Y) (F : MvPowerSeries Y R) : pdL (L ++ L') F = pdL L' (pdL L F) := by sorry
