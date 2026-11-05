-- Prove2me | Theorems.Thm_GeneralPieces_GenF_coeff_JpV
-- name    : GeneralPieces.GenF.coeff_JpV
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:32:54.088188+00:00
-- url     : https://prove2.me/theorems/5d508a3c-d788-4552-aa3d-986d62da3ed5
-- title:
--   Gen F: coeff Jp V
-- statement:
--   The Gen F construction uses the coeff Jp V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L270-L270
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Bra.lean#L270-L270

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

theorem GeneralPieces.GenF.coeff_JpV (n : ℕ) (y : ℤ) : (JpV n).coeff y = if 0 ≤ y then MvPolynomial.C (C (bet n (y + n) : ℚ)) * MvPolynomial.X (y + n).toNat else 0 := by sorry
