-- Prove2me | Theorems.Thm_GeneralPieces_Bits_p_pred_lt
-- name    : GeneralPieces.Bits.p_pred_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:37:46.582199+00:00
-- url     : https://prove2.me/theorems/4303e1bb-c038-417e-b522-0e2ace0d65bf
-- title:
--   Bits: p pred lt
-- statement:
--   p(h−1) < 2^λ: by the choice of h if h > 2, and because p(1) = 1 if h = 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L37-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bits.lean#L37-L39

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Sizes
import Definitions.Def_ClauseBound_Part_Bounds
import Definitions.Def_GeneralPieces_Ring_Bits
import Theorems.Thm_ClauseBound_Part_Bits_p_pred_lt

set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Bits
open AppHalfPieces Finset Partitions Real GeneralPieces.Lex GeneralPieces.Sizes
variable {B C : ℝ}

theorem GeneralPieces.Bits.p_pred_lt {lam : ℕ} (hl : 1 ≤ lam) : p (AppHalfPieces.hOf lam - 1) < 2 ^ lam := by sorry
