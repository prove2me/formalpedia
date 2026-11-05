-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Normal_emb_smul_mo
-- name    : GeneralPieces.GenF.Normal.emb_smul_mo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:28.840197+00:00
-- url     : https://prove2.me/theorems/2f817b34-d57b-40c7-aa43-c352d4aabc91
-- title:
--   Normal: emb smul mo
-- statement:
--   The Normal construction uses the emb smul mo property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L132-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L132-L138

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

theorem GeneralPieces.GenF.Normal.emb_smul_mo (q : ℚ) (x : ℤ) : emb (q • mo x 0) = HahnSeries.C (MvPolynomial.C (C q * T x)) := by sorry
