-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y_constantCoeff_outer
-- name    : GeneralPieces.GenF.Y.constantCoeff_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:10:50.925241+00:00
-- url     : https://prove2.me/theorems/6758c3d9-4abc-4e2e-92aa-e76a3680c422
-- title:
--   Y: constant Coeff outer
-- statement:
--   The Y construction uses the constant Coeff outer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L148-L149
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L148-L149

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y
open GeneralPieces.GenF.Y

theorem GeneralPieces.GenF.Y.constantCoeff_outer (rd : Bool) (σ' : Multiset ℕ) : constantCoeff (outer rd σ') = (σ'.map tT).prod := by sorry
