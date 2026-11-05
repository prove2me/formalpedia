-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Normal_sel_add
-- name    : GeneralPieces.GenF.Normal.sel_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:34:41.074291+00:00
-- url     : https://prove2.me/theorems/cb1c9d39-5713-4d4c-9d04-126de85eb569
-- title:
--   Normal: sel add
-- statement:
--   The Normal construction uses the sel add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L113-L114
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L113-L114

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_GeneralPieces_GenF_Normal
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial

theorem GeneralPieces.GenF.Normal.sel_add {R : Type} [AddZeroClass R] (rd : Bool) (f g : ℕ → R) (i : X) : sel rd f 0 i + sel rd 0 g i = sel rd f g i := by sorry
