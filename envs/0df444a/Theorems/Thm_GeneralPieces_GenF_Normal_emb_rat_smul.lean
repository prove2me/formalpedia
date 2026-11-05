-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Normal_emb_rat_smul
-- name    : GeneralPieces.GenF.Normal.emb_rat_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:22.718877+00:00
-- url     : https://prove2.me/theorems/ef5eb2a6-c19e-4f9f-b0be-1d9e192a052d
-- title:
--   Normal: emb rat smul
-- statement:
--   The Normal construction uses the emb rat smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L127-L130
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L127-L130

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

theorem GeneralPieces.GenF.Normal.emb_rat_smul (q : ℚ) (s : S) : emb (q • s) = q • emb s := by sorry
