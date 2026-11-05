-- Prove2me | Theorems.Thm_GeneralPieces_GenF_sel_xi
-- name    : GeneralPieces.GenF.sel_xi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:35.7502+00:00
-- url     : https://prove2.me/theorems/81fcfef4-e0b1-4b2e-9e70-506dc643fc26
-- title:
--   Gen F: sel xi
-- statement:
--   The Gen F construction uses the sel xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L35-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L35-L37

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
variable {R : Type} [Zero R]

theorem GeneralPieces.GenF.sel_xi (rd : Bool) (f g : ℕ → R) {n : ℕ} (hn : 1 ≤ n) : sel rd f g (xi rd n) = f n := by sorry
