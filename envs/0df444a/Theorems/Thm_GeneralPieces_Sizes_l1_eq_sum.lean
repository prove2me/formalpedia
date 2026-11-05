-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_l1_eq_sum
-- name    : GeneralPieces.Sizes.l1_eq_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:22:39.550355+00:00
-- url     : https://prove2.me/theorems/e1e4c4ab-ce7b-49ff-a4f9-0f62bb66da5c
-- title:
--   Sizes: l1 eq sum
-- statement:
--   The Sizes construction uses the l1 eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L222-L223
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L222-L223

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.l1_eq_sum {a : V} {S : Finset (ℕ+ →₀ ℕ)} (hS : a.support ⊆ S) : l1 a = ∑ m ∈ S, |coeff m a| := by sorry
