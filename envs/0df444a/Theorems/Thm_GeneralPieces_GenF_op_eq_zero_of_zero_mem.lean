-- Prove2me | Theorems.Thm_GeneralPieces_GenF_op_eq_zero_of_zero_mem
-- name    : GeneralPieces.GenF.op_eq_zero_of_zero_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:11:49.020625+00:00
-- url     : https://prove2.me/theorems/f7565314-51b7-48e3-9520-c429148c0a86
-- title:
--   Gen F: op eq zero of zero mem
-- statement:
--   t₀ does not occur: the entries of t^ν[r] in the rows of the monomials with t₀ vanish.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L191-L205
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y.lean#L191-L205

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open Y

theorem GeneralPieces.GenF.op_eq_zero_of_zero_mem (b : List ℕ) (r : ℤ) {τ σ : Multiset ℕ} (hτ : 0 ∈ τ) (hσ : 0 ∉ σ) : op b r τ σ = 0 := by sorry
