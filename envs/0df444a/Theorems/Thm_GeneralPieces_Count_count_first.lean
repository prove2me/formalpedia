-- Prove2me | Theorems.Thm_GeneralPieces_Count_count_first
-- name    : GeneralPieces.Count.count_first
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:00:30.542459+00:00
-- url     : https://prove2.me/theorems/db615132-5bbc-4282-acf1-2dc8390cb66d
-- title:
--   Count: count first
-- statement:
--   The first inequality of the display, in real variables: X = Ξ, s = 2^{2N/K}, u = 2^{cλ}, a = |𝓘|^{|R|}
--   ≤ Ξ^A, κ = K^g ≤ Ξ^G, q = (2|𝓘|+2)·2^{cλ} ≤ Ξ^{c+1}τ, τ = u·Ξ^{C₂}, D₁ = (c+4)C₁. Every sum of two
--   numbers is bounded by Ξ times the larger bound («a sum of numbers that are at least 2 is at most
--   their product»).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Count.lean#L32-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Rec/Count.lean#L32-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_Remarks
import Definitions.Def_ClauseBound_Gen_Seq
import Definitions.Def_GeneralPieces_Rec_Count
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Count
open Levels.Gen ClauseBound.Gen

theorem GeneralPieces.Count.count_first (X T s u a κ q : ℝ) (A G c D₁ C₂ C₃ : ℕ) (hX : 2 ≤ X) (hT : 1 ≤ T) (hs : 1 ≤ s) (hu : 1 ≤ u) (ha : a ≤ X ^ A)
    (hκ0 : 0 ≤ κ) (hκ : κ ≤ X ^ G) (hq : q ≤ X ^ (c + 1) * (u * X ^ C₂)) :
    a * ((κ + T * s * (u * X ^ C₂)) * X ^ D₁ + 2 * X ^ C₃) + q + X ^ C₃ ≤ X ^ (A + G + (D₁ + C₂ + C₃ + c + 4)) * T * (s * u) := by sorry
