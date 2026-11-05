-- Prove2me | Theorems.Thm_GeneralPieces_GenF_support_bra
-- name    : GeneralPieces.GenF.support_bra
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:32:16.068836+00:00
-- url     : https://prove2.me/theorems/fd654666-1a60-4805-b5bd-b595a1af8453
-- title:
--   Gen F: support bra
-- statement:
--   The Gen F construction uses the support bra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L109-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L109-L109

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Defs
import Definitions.Def_GeneralPieces_GenF_Coeff
import Definitions.Def_GeneralPieces_GenF_Bra
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.support_bra (σ : Multiset ℕ) (f : Tv) : (bra σ f).support ⊆ f.support := by sorry
