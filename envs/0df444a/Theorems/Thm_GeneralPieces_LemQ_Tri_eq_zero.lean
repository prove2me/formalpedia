-- Prove2me | Theorems.Thm_GeneralPieces_LemQ_Tri_eq_zero
-- name    : GeneralPieces.LemQ.Tri.eq_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:21:24.889208+00:00
-- url     : https://prove2.me/theorems/090ef3c9-5516-4516-b5e5-c3abcc5f4165
-- title:
--   Tri: eq zero
-- statement:
--   "So let a = t^μ with |μ| = h' ≤ h and b = t^ν": a claim T(a, b, f) = 0 that is linear in a, b
--   and f holds for all a = Σ_{h' ≤ h} ā_{h'}, b ∈ V_h and f ∈ V_E if it holds for monomials.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L173-L181
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Ring/LemmaQ.lean#L173-L181

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
open GeneralPieces.LemQ.Tri
variable {T T' : V → V → V → V}

theorem GeneralPieces.LemQ.Tri.eq_zero (hT : Tri T) {h E : ℕ} (hmon : ∀ μ ν σ : Ptn, wt μ ≤ h → wt ν = h → wt σ = E → T (tpow μ) (tpow ν) (tpow σ) = 0)
    {a b f : V} (ha : WtLe h a) (hb : b ∈ VE h) (hf : f ∈ VE E) : T a b f = 0 := by sorry
