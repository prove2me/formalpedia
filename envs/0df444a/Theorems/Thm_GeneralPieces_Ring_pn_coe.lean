-- Prove2me | Theorems.Thm_GeneralPieces_Ring_pn_coe
-- name    : GeneralPieces.Ring.pn_coe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:28:55.562111+00:00
-- url     : https://prove2.me/theorems/e3524a83-f543-4b73-a13d-3d2128f6866a
-- title:
--   Ring: pn coe
-- statement:
--   The positive integer |k| as a natural number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L49-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L49-L49

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.pn_coe {k : ℤ} (hk : k ≠ 0) : ((pn k : ℕ+) : ℕ) = k.natAbs := by sorry
