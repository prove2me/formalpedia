-- Prove2me | Theorems.Thm_GeneralPieces_GenF_constantCoeff_braW
-- name    : GeneralPieces.GenF.constantCoeff_braW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:07.914561+00:00
-- url     : https://prove2.me/theorems/7dbfa355-721b-48f5-9460-3debdf06b017
-- title:
--   Gen F: constant Coeff bra W
-- statement:
--   The Gen F construction uses the constant Coeff bra W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L352-L352
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L352-L352

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

theorem GeneralPieces.GenF.constantCoeff_braW (σ : Multiset ℕ) (w : W) : MvPowerSeries.constantCoeff (braW σ w) = bra σ (MvPowerSeries.constantCoeff w) := by sorry
