-- Prove2me | Theorems.Thm_GeneralPieces_GenF_braW_embW_mul
-- name    : GeneralPieces.GenF.braW_embW_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:33:13.583142+00:00
-- url     : https://prove2.me/theorems/986da1e5-43a6-4490-af36-3db9cd41cd60
-- title:
--   Gen F: bra W emb W mul
-- statement:
--   Power series without the t_k may be taken out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L373-L378
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L373-L378

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

theorem GeneralPieces.GenF.braW_embW_mul (σ : Multiset ℕ) (e : PS) (w : W) : braW σ (embW e * w) = e * braW σ w := by sorry
