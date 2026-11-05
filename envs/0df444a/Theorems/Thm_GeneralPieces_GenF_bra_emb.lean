-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_emb
-- name    : GeneralPieces.GenF.bra_emb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:46.573066+00:00
-- url     : https://prove2.me/theorems/d679c61a-49f0-4913-8523-cd347c44d1c5
-- title:
--   Gen F: bra emb
-- statement:
--   The Gen F construction uses the bra emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L148-L156
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L148-L156

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

theorem GeneralPieces.GenF.bra_emb (σ : Multiset ℕ) (s : S) : bra σ (emb s) = if σ = 0 then s else 0 := by sorry
