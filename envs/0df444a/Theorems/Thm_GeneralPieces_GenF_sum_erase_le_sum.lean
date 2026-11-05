-- Prove2me | Theorems.Thm_GeneralPieces_GenF_sum_erase_le_sum
-- name    : GeneralPieces.GenF.sum_erase_le_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:12:36.612877+00:00
-- url     : https://prove2.me/theorems/d74aba5d-6462-4076-acb7-8c46a1763e9c
-- title:
--   Gen F: sum erase le sum
-- statement:
--   The Gen F construction uses the sum erase le sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L137-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/Y2.lean#L137-L141

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_DDComm
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_Eth_16a5ce4_GeneralPieces_GenF_Y2_Definitions
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson LaurentPolynomial Finset

theorem GeneralPieces.GenF.sum_erase_le_sum (σ : Multiset ℕ) (l : ℕ) : (σ.erase l).sum ≤ σ.sum := by sorry
