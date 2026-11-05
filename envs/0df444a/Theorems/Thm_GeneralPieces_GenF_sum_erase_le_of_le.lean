-- Prove2me | Theorems.Thm_GeneralPieces_GenF_sum_erase_le_of_le
-- name    : GeneralPieces.GenF.sum_erase_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:07:49.692648+00:00
-- url     : https://prove2.me/theorems/f43a04a0-08de-47ed-81ec-a3547fb80de4
-- title:
--   Gen F: sum erase le of le
-- statement:
--   The Gen F construction uses the sum erase le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L85-L89
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/GenF/NormalL.lean#L85-L89

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Products
import Definitions.Def_GeneralPieces_GenF_Bra
import Definitions.Def_GeneralPieces_GenF_NormalL
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson

theorem GeneralPieces.GenF.sum_erase_le_of_le {σ : Multiset ℕ} {E : ℕ} (h : σ.sum ≤ E) (l : ℕ) : (σ.erase l).sum ≤ E := by sorry
