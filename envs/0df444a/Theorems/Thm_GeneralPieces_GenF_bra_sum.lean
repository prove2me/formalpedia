-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_sum
-- name    : GeneralPieces.GenF.bra_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:32:45.36188+00:00
-- url     : https://prove2.me/theorems/96737d34-7cee-4d1e-9230-653048af9bf7
-- title:
--   Gen F: bra sum
-- statement:
--   The Gen F construction uses the bra sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L127-L127
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L127-L127

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

theorem GeneralPieces.GenF.bra_sum {ι : Type} (σ : Multiset ℕ) (s : Finset ι) (F : ι → Tv) : bra σ (∑ i ∈ s, F i) = ∑ i ∈ s, bra σ (F i) := by sorry
