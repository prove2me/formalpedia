-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pderiv_C_mul
-- name    : GeneralPieces.GenF.pderiv_C_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:57.078044+00:00
-- url     : https://prove2.me/theorems/d3e6c4cf-627a-4159-8124-6e42d618b9ad
-- title:
--   Gen F: pderiv C mul
-- statement:
--   The Gen F construction uses the pderiv C mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Borel.lean#L65-L66

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

theorem GeneralPieces.GenF.pderiv_C_mul (i : Y) (c : R) (F : MvPowerSeries Y R) : pderiv R i (C c * F) = C c * pderiv R i F := by sorry
