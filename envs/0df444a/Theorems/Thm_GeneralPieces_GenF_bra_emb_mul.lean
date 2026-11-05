-- Prove2me | Theorems.Thm_GeneralPieces_GenF_bra_emb_mul
-- name    : GeneralPieces.GenF.bra_emb_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:44.772854+00:00
-- url     : https://prove2.me/theorems/61bcde8d-b450-4311-a6cf-7d2c665f1bd3
-- title:
--   Gen F: bra emb mul
-- statement:
--   Series without the t_k may be taken out.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L142-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L142-L146

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

theorem GeneralPieces.GenF.bra_emb_mul (σ : Multiset ℕ) (s : S) (f : Tv) : bra σ (emb s * f) = s * bra σ f := by sorry
