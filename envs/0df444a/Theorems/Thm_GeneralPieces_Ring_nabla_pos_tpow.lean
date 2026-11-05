-- Prove2me | Theorems.Thm_GeneralPieces_Ring_nabla_pos_tpow
-- name    : GeneralPieces.Ring.nabla_pos_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:31:26.677974+00:00
-- url     : https://prove2.me/theorems/71b6141d-23a0-417d-bb10-5cd6a44c5791
-- title:
--   Ring: nabla pos tpow
-- statement:
--   ∇_k on a monomial, k ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L80-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L80-L84

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

theorem GeneralPieces.Ring.nabla_pos_tpow {k : ℤ} (hk : 0 < k) (σ : Ptn) : nabla k (tpow σ) = ((k : ℚ) * σ.count (pn k)) • tpow (σ.erase (pn k)) := by sorry
