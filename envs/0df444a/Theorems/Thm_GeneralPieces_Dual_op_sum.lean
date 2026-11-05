-- Prove2me | Theorems.Thm_GeneralPieces_Dual_op_sum
-- name    : GeneralPieces.Dual.op_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:35:11.297003+00:00
-- url     : https://prove2.me/theorems/69350204-3218-494c-ae31-5d36a439b41d
-- title:
--   Dual: op sum
-- statement:
--   a[r] is linear in a, for finite sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L192-L197
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L192-L197

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_Dual
import Definitions.Def_GeneralPieces_Ring_Dual
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Dual
open Finset MvPolynomial AppHalfPieces

theorem GeneralPieces.Dual.op_sum {ι : Type} (s : Finset ι) (c : ι → ℚ) (g : ι → V) (r : ℤ) (f : V) :
    op (∑ x ∈ s, c x • g x) r f = ∑ x ∈ s, c x • op (g x) r f := by sorry
