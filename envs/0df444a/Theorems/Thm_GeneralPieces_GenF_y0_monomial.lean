-- Prove2me | Theorems.Thm_GeneralPieces_GenF_y0_monomial
-- name    : GeneralPieces.GenF.y0_monomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:15.120019+00:00
-- url     : https://prove2.me/theorems/0b515cad-187a-41b2-9f5a-a622cda1309f
-- title:
--   Gen F: y0 monomial
-- statement:
--   On the monomial t^τ: the entry (σ, τ) of the matrix of a[r], r = |σ| − |τ|, times u^{r−|a|}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L56-L90
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L56-L90

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

theorem GeneralPieces.GenF.y0_monomial (a : List ℕ) : ∀ σ τ : Multiset ℕ, y0 a σ (MvPolynomial.monomial (Multiset.toFinsupp τ) 1) =
    C ((op a ((σ.sum : ℤ) - τ.sum) σ τ : ℤ) : ℚ) * T ((σ.sum : ℤ) - τ.sum - a.sum) := by sorry
