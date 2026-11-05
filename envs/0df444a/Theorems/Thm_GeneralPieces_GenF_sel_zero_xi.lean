-- Prove2me | Theorems.Thm_GeneralPieces_GenF_sel_zero_xi
-- name    : GeneralPieces.GenF.sel_zero_xi
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:05:36.799705+00:00
-- url     : https://prove2.me/theorems/e8315dfe-c872-4c2a-8622-8f49b6cdfa94
-- title:
--   Gen F: sel zero xi
-- statement:
--   The Gen F construction uses the sel zero xi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L57-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L57-L59

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

theorem GeneralPieces.GenF.sel_zero_xi (rd : Bool) (g : ℕ → R) (n : ℕ) : sel rd 0 g (xi rd n) = 0 := by sorry
