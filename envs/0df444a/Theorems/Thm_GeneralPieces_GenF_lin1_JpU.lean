-- Prove2me | Theorems.Thm_GeneralPieces_GenF_lin1_JpU
-- name    : GeneralPieces.GenF.lin1_JpU
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:06:20.142203+00:00
-- url     : https://prove2.me/theorems/6437a085-8686-421e-afce-df9233c773b3
-- title:
--   Gen F: lin1 Jp U
-- statement:
--   The Gen F construction uses the lin1 Jp U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L307-L314
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L307-L314

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

theorem GeneralPieces.GenF.lin1_JpU (E n : ℕ) : Lin1 (HahnSeries.C (JpU E n)) := by sorry
