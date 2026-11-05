-- Prove2me | Theorems.Thm_NamesInOrder_length_le_sq
-- name    : NamesInOrder.length_le_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:17:11.270196+00:00
-- url     : https://prove2.me/theorems/a463b958-a0a1-4f2a-ac7e-4fa0905181e1
-- title:
--   Names In Order: length le sq
-- statement:
--   If every variable occurs and there is at least one clause, the input has at most 6·(km)² bits (k
--   ≥ 1; n may be 0).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L65-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/maintheorem/NamesInOrder/Arith.lean#L65-L75

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_NamesInOrder_Defs
import Definitions.Def_MinOfBounds_Arith
import Definitions.Def_PairsToBound_Arith
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Forms
import Definitions.Def_ClauseBound_Alg_End
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_NamesInOrder_Arith
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open NamesInOrder
open Turing MainTheoremForms VariableBound.Paper MinOfBounds PairsToBound
open Sat3 (CNF)

theorem NamesInOrder.length_le_sq {k n : ℕ} {φ : CNF n} (hk : 1 ≤ k) (hm : 1 ≤ φ.length) (hφ : SatK.IsKCNF k φ) (ho : SatM.AllOccur φ) : (SatM.enc k φ).length ≤ 6 * (k * φ.length) ^ 2 := by sorry
