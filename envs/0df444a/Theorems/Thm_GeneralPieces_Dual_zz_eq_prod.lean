-- Prove2me | Theorems.Thm_GeneralPieces_Dual_zz_eq_prod
-- name    : GeneralPieces.Dual.zz_eq_prod
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:36:05.579853+00:00
-- url     : https://prove2.me/theorems/8a637c1e-9371-42cf-85dd-fd198f469905
-- title:
--   Dual: zz eq prod
-- statement:
--   The Dual construction uses the zz eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L421-L425
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L421-L425

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

theorem GeneralPieces.Dual.zz_eq_prod {ν : Ptn} {S : Finset ℕ+} (h : ν.toFinset ⊆ S) : zz ν = ∏ k ∈ S, (k : ℕ) ^ ν.count k * (ν.count k).factorial := by sorry
