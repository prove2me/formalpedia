-- Prove2me | Theorems.Thm_GeneralPieces_Dual_coe_snoc
-- name    : GeneralPieces.Dual.coe_snoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:25:18.29447+00:00
-- url     : https://prove2.me/theorems/fe9e19cd-7c52-4620-bcd4-2a51ceb9b073
-- title:
--   Dual: coe snoc
-- statement:
--   The Dual construction uses the coe snoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L388-L389
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L388-L389

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

theorem GeneralPieces.Dual.coe_snoc (μ : List ℕ+) (n : ℕ+) : ((μ ++ [n] : List ℕ+) : Multiset ℕ+) = n ::ₘ (μ : Multiset ℕ+) := by sorry
