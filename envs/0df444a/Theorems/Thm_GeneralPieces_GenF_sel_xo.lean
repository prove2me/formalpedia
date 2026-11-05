-- Prove2me | Theorems.Thm_GeneralPieces_GenF_sel_xo
-- name    : GeneralPieces.GenF.sel_xo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:31:56.813502+00:00
-- url     : https://prove2.me/theorems/bda50bc4-383f-4147-a094-5d48e941ed34
-- title:
--   Gen F: sel xo
-- statement:
--   The Gen F construction uses the sel xo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L39-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L39-L41

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

theorem GeneralPieces.GenF.sel_xo (rd : Bool) (f g : ℕ → R) {n : ℕ} (hn : 1 ≤ n) : sel rd f g (xo rd n) = g n := by sorry
