-- Prove2me | Theorems.Thm_GeneralPieces_Ring_wt_erase
-- name    : GeneralPieces.Ring.wt_erase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:30:16.596916+00:00
-- url     : https://prove2.me/theorems/90ed24dd-ec9b-452c-a5c3-4aae1cc66295
-- title:
--   Ring: wt erase
-- statement:
--   Without a part l, the weight is smaller by l.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L158-L160
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/Bridge.lean#L158-L160

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Defs
import Definitions.Def_ClauseBound_Boson_Text
import Mathlib.RingTheory.Derivation.Lie
import Definitions.Def_GeneralPieces_Ring_Bridge
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Ring
open AppHalfPieces MvPolynomial Finset

theorem GeneralPieces.Ring.wt_erase {σ : Ptn} {l : ℕ+} (h : l ∈ σ) : wt (σ.erase l) + l = wt σ := by sorry
