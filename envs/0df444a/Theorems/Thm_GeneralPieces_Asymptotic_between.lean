-- Prove2me | Theorems.Thm_GeneralPieces_Asymptotic_between
-- name    : GeneralPieces.Asymptotic.between
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:44:59.929193+00:00
-- url     : https://prove2.me/theorems/62fb2eb4-0740-4aa7-a6ad-7babae89d13b
-- title:
--   Asymptotic: between
-- statement:
--   «… a number between 0.85·ρ^ℓ and ρ^ℓ lies in [e_ℓ, 2e_ℓ].»
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Asymptotic.lean#L32-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/GeneralPieces/Num/Asymptotic.lean#L32-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Num_PartA
import Definitions.Def_GeneralPieces_Num_Asymptotic
set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Asymptotic
open Levels.Gen ClauseBound.Gen GeneralPieces.PartA

theorem GeneralPieces.Asymptotic.between (ρ : ℝ) (x₀ l : ℕ) (t : ℝ) (hρ : 1 / 2 ≤ ρ) (hx : 18 ≤ x₀) (h1 : 0.85 * ρ ^ l ≤ t) (h2 : t ≤ ρ ^ l) :
    e ρ x₀ l ≤ t ∧ t ≤ 2 * e ρ x₀ l := by sorry
