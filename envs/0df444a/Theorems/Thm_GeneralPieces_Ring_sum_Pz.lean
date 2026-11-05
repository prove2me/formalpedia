-- Prove2me | Theorems.Thm_GeneralPieces_Ring_sum_Pz
-- name    : GeneralPieces.Ring.sum_Pz
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:16.909145+00:00
-- url     : https://prove2.me/theorems/505d5e20-0646-4f0f-b6df-e12bc99ec194
-- title:
--   Ring: sum Pz
-- statement:
--   The Ring construction uses the sum Pz property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L149-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Op.lean#L149-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_OpFacts
import Definitions.Def_GeneralPieces_Ring_Op
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.sum_Pz {A : Type} [AddCommMonoid A] (m : ℤ) (G : Multiset ℕ → A) : ∑ τ ∈ ClauseBound.Boson.Pz m, G τ = ∑ τ ∈ ptnsZ m, G (toN τ) := by sorry
