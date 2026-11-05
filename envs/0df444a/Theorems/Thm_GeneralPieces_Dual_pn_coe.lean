-- Prove2me | Theorems.Thm_GeneralPieces_Dual_pn_coe
-- name    : GeneralPieces.Dual.pn_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:52.170719+00:00
-- url     : https://prove2.me/theorems/bc470c0f-656c-417e-9e19-cc24da934771
-- title:
--   Dual: pn coe
-- statement:
--   The Dual construction uses the pn coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L354-L354
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L354-L354

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
import Theorems.Thm_GeneralPieces_Ring_pn_coe

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.pn_coe (n : ℕ+) : pn (n : ℤ) = n := by sorry
