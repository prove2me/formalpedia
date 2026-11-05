-- Prove2me | Theorems.Thm_GeneralPieces_Sizes_abs_binom_le
-- name    : GeneralPieces.Sizes.abs_binom_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:26:31.411359+00:00
-- url     : https://prove2.me/theorems/4e464379-1d21-491f-86c8-d394fbdb17f9
-- title:
--   Sizes: abs binom le
-- statement:
--   The Sizes construction uses the abs binom le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L123-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Sizes.lean#L123-L126

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_GeneralPieces_Ring_Lex
import Definitions.Def_ClauseBound_Boson_Size
import Definitions.Def_GeneralPieces_Ring_Sizes
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Sizes
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.Sizes.abs_binom_le (k : ℤ) (n : ℕ+) : |binom k ((n : ℤ) - 1)| ≤ 2 ^ (k.natAbs + ((n : ℕ) - 1)) := by sorry
