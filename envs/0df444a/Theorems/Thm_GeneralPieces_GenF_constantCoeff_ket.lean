-- Prove2me | Theorems.Thm_GeneralPieces_GenF_constantCoeff_ket
-- name    : GeneralPieces.GenF.constantCoeff_ket
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:44.319317+00:00
-- url     : https://prove2.me/theorems/a989906d-8624-4303-a0c5-bf4cdf730e37
-- title:
--   Gen F: constant Coeff ket
-- statement:
--   The Gen F construction uses the constant Coeff ket property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L61-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L61-L68

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson

theorem GeneralPieces.GenF.constantCoeff_ket (rd : Bool) (σ' : Multiset ℕ) : MvPowerSeries.constantCoeff (ket rd σ') = (σ'.map tT).prod := by sorry
