-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_angle_tpow
-- name    : GeneralPieces.LemQ.angle_tpow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:36:16.584189+00:00
-- url     : https://prove2.me/theorems/a236fa68-a360-4a26-b84d-75fa8912b4e8
-- title:
--   Lem Q: angle tpow
-- statement:
--   "Then a^⟨i⟩ = C(H, i)·a with H = h' + h", for a = t^μ with |μ| = h' ≤ h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L262-L265
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L262-L265

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Ring_Basic
import Definitions.Def_GeneralPieces_Ring_LemmaQ
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.LemQ
open AppHalfPieces MvPolynomial Finset GeneralPieces.Ring

theorem GeneralPieces.LemQ.angle_tpow {h : ℕ} (i : ℕ) {μ : Ptn} (hμ : wt μ ≤ h) : angle h i (tpow μ) = ((wt μ + h).choose i : ℚ) • tpow μ := by sorry
