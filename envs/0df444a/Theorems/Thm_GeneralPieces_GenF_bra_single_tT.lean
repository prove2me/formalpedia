-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_single_tT
-- name    : GeneralPieces.GenF.bra_single_tT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:10.103634+00:00
-- url     : https://prove2.me/theorems/1a1d9f0f-0f61-4443-8fc2-0e727bb21e7b
-- title:
--   Gen F: bra single t T
-- statement:
--   The Gen F construction uses the bra single t T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L244-L254
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L244-L254

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

theorem GeneralPieces.GenF.bra_single_tT (l k : ℕ) : bra {l} (tT k) = if l = k then 1 else 0 := by sorry
