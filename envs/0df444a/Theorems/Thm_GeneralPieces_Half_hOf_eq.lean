-- Prove2me | Theorems.Thm_GeneralPieces_Half_hOf_eq
-- name    : GeneralPieces.Half.hOf_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:39:39.91347+00:00
-- url     : https://prove2.me/theorems/f9e17457-c458-486d-a44b-82c46d3ff9eb
-- title:
--   Half: h Of eq
-- statement:
--   The least h ≥ 2 with p(h) ≥ 2^λ: the number h of Appendix B is the number of the programs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L140-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/Order.lean#L140-L145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Half_List
import Definitions.Def_ClauseBound_Inst_HalfEnc
import Definitions.Def_GeneralPieces_Half_Order
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Half
open AppHalfPieces Finset ClauseBound.Part GeneralPieces.Ring Groundwork ClauseBound.Alg ClauseBound.Inst.Half

theorem GeneralPieces.Half.hOf_eq (lam : ℕ) : AppHalfPieces.hOf lam = ClauseBound.Part.hOf lam := by sorry
