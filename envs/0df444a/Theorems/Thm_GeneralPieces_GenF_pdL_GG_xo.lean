-- Prove2me | Theorems.Thm_GeneralPieces_GenF_pdL_GG_xo
-- name    : GeneralPieces.GenF.pdL_GG_xo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:31.34272+00:00
-- url     : https://prove2.me/theorems/04bf1a63-e78b-4597-9d9f-46297a79185a
-- title:
--   Gen F: pd L GG xo
-- statement:
--   The Gen F construction uses the pd L GG xo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L132-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L132-L135

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

theorem GeneralPieces.GenF.pdL_GG_xo (rd : Bool) (E : ℕ) (σ : Multiset ℕ) (b : List ℕ) : ∀ w : W, pdL (b.map (xo rd)) (GG rd E σ w) = GG rd E σ (pdL (b.map (xo rd)) w) := by sorry
