-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Normal_mapD_embW
-- name    : GeneralPieces.GenF.Normal.mapD_embW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:05.945991+00:00
-- url     : https://prove2.me/theorems/22b7a5d1-f039-48bb-90bc-e3ecf74eeadf
-- title:
--   Normal: map D emb W
-- statement:
--   The Normal construction uses the map D emb W property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L116-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L116-L119

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

theorem GeneralPieces.GenF.Normal.mapD_embW (rd : Bool) (i : X) (e : PS) : mapD (DD rd i) (embW e) = 0 := by sorry
