-- Prove2me | Theorems.Thm_GeneralPieces_Dual_mem_posTuples
-- name    : GeneralPieces.Dual.mem_posTuples
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:50.467727+00:00
-- url     : https://prove2.me/theorems/4d8764a6-f9f0-43e7-9e89-c0c1b2c769f1
-- title:
--   Dual: mem pos Tuples
-- statement:
--   These are the lists of r integers k_i ≥ 1 with sum h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L123-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Dual.lean#L123-L131

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

theorem GeneralPieces.Dual.mem_posTuples (r h : ℕ) (ks : List ℤ) : ks ∈ posTuples r h ↔ ks.length = r ∧ (∀ k ∈ ks, 1 ≤ k) ∧ ks.sum = h := by sorry
