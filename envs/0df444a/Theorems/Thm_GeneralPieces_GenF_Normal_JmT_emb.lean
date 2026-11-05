-- Prove2me | Theorems.Thm_GeneralPieces_GenF_Normal_JmT_emb
-- name    : GeneralPieces.GenF.Normal.JmT_emb
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:08:19.815906+00:00
-- url     : https://prove2.me/theorems/521a5616-c750-4ffb-ae45-7d201bb84277
-- title:
--   Normal: Jm T emb
-- statement:
--   J_n^-(u) vanishes on the constant polynomials.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L102-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Normal.lean#L102-L105

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

theorem GeneralPieces.GenF.Normal.JmT_emb (n : ℕ) (s : S) : JmT n (emb s) = 0 := by sorry
