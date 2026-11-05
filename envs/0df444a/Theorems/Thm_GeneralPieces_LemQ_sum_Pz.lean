-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_sum_Pz
-- name    : GeneralPieces.LemQ.sum_Pz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:22:06.475119+00:00
-- url     : https://prove2.me/theorems/712175bf-74c7-4e89-8d5a-08261eed3b4d
-- title:
--   Lem Q: sum Pz
-- statement:
--   A sum over the multisets of positive natural numbers with sum m is a sum over the partitions of
--   m.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L277-L285
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L277-L285

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.LemQ.sum_Pz (m : ℤ) (F : Multiset ℕ → ℤ) : ∑ τ ∈ ClauseBound.Boson.Pz m, F τ = ∑ τ ∈ ptnsZ m, F (toN τ) := by sorry
