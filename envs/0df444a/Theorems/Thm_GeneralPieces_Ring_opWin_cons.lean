-- Prove2me | Theorems.Thm_GeneralPieces_Ring_opWin_cons
-- name    : GeneralPieces.Ring.opWin_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:33:36.909878+00:00
-- url     : https://prove2.me/theorems/7a37ea12-5a6e-4a76-90ee-946bdb15e5dd
-- title:
--   Ring: op Win cons
-- statement:
--   The recursion (O2) for the finite sums.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L201-L220
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/OpFacts.lean#L201-L220

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_OpFacts
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.opWin_cons (n : ℕ+) (μ : List ℕ+) (M : ℕ) (r : ℤ) (f : V) : opWin (n :: μ) M r f =
    ∑ l ∈ Icc 1 M, (binom ((l : ℤ) - 1) ((n : ℤ) - 1) : ℚ) • nabla (-(l : ℤ)) (opWin μ M (r - l) f) +
      ∑ k ∈ Icc 1 M, (binom (-(k : ℤ) - 1) ((n : ℤ) - 1) : ℚ) • opWin μ M (r + k) (nabla k f) := by sorry
