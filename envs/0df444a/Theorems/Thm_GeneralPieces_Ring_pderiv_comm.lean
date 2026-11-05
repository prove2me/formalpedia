-- Prove2me | Theorems.Thm_GeneralPieces_Ring_pderiv_comm
-- name    : GeneralPieces.Ring.pderiv_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:01:27.468775+00:00
-- url     : https://prove2.me/theorems/2790147d-1355-4b73-888f-6fad41cba900
-- title:
--   Ring: pderiv comm
-- statement:
--   ∂/∂t_i and ∂/∂t_j commute.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L52-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L52-L59

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

theorem GeneralPieces.Ring.pderiv_comm (i j : ℕ+) (f : V) : pderiv i (pderiv j f) = pderiv j (pderiv i f) := by sorry
