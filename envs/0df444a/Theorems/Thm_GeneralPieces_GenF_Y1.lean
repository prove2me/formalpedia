-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Y1
-- name    : GeneralPieces.GenF.Y1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:11:38.934556+00:00
-- url     : https://prove2.me/theorems/4f1e0f74-b0e6-47b4-aa09-57415c264ebd
-- title:
--   Gen F: Y1
-- statement:
--   The same with the definitions written out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L185-L188
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L185-L188

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

theorem GeneralPieces.GenF.Y1 (rd : Bool) (b : List ℕ) (hb : Pos b) (τ σ' : Multiset ℕ) :
    bra τ (fac (aL (xo rd) b) • coeff (aL (xo rd) b) (expW (Bp rd) * ket rd σ')) =
      ((op b ((τ.sum : ℤ) - σ'.sum) τ σ' : ℤ) : ℚ) • mo 0 ((τ.sum : ℤ) - σ'.sum - b.sum) := by sorry
