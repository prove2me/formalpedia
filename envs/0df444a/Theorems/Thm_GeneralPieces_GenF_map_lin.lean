-- Prove2me | Theorems.Thm_GeneralPieces_GenF_map_lin
-- name    : GeneralPieces.GenF.map_lin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:32:06.688586+00:00
-- url     : https://prove2.me/theorems/e829934b-258c-4c24-9ae7-2ab9e69c3f50
-- title:
--   Gen F: map lin
-- statement:
--   The Gen F construction uses the map lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L77-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L77-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial
variable {Y A : Type} [CommRing A]

theorem GeneralPieces.GenF.map_lin {A' : Type} [CommRing A'] (φ : A →+* A') (c : Y → A) : MvPowerSeries.map φ (lin c) = lin fun i => φ (c i) := by sorry
