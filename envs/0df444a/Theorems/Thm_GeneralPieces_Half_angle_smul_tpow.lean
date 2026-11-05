-- Prove2me | Theorems.Thm_GeneralPieces_Half_angle_smul_tpow
-- name    : GeneralPieces.Half.angle_smul_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:39:45.219365+00:00
-- url     : https://prove2.me/theorems/5883146a-02b0-45a4-8ff8-b54f4c43d654
-- title:
--   Half: angle smul tpow
-- statement:
--   (q·t^μ)^⟨i⟩ = C(|μ| + h, i)·q·t^μ for |μ| ≤ h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L160-L165
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Half/List.lean#L160-L165

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Op
import Definitions.Def_ClauseBound_Boson_HalfList
import Definitions.Def_GeneralPieces_Half_List
set_option autoImplicit false
section
section
open GeneralPieces
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring
open GeneralPieces.Half

theorem GeneralPieces.Half.angle_smul_tpow (h i : ℕ) (q : ℚ) {μ : Ptn} (hμ : wt μ ≤ h) : angle h i (q • tpow μ) = (q * ((wt μ + h).choose i : ℚ)) • tpow μ := by sorry
