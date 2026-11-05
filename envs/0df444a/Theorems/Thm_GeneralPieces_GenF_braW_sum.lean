-- Prove2me | Theorems.Thm_GeneralPieces_GenF_braW_sum
-- name    : GeneralPieces.GenF.braW_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:27.104094+00:00
-- url     : https://prove2.me/theorems/dcd9d81e-641d-45cd-85ce-a6dc35e6420d
-- title:
--   Gen F: bra W sum
-- statement:
--   The Gen F construction uses the bra W sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L368-L368
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L368-L368

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

theorem GeneralPieces.GenF.braW_sum {ι : Type} (σ : Multiset ℕ) (s : Finset ι) (F : ι → W) : braW σ (∑ i ∈ s, F i) = ∑ i ∈ s, braW σ (F i) := by sorry
