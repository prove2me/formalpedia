-- Prove2me | Theorems.Thm_Groundwork_RebalanceArith_size_le
-- name    : Groundwork.RebalanceArith.size_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:18:29.436219+00:00
-- url     : https://prove2.me/theorems/cd71de22-e0a6-42d9-b803-20a09c162ade
-- title:
--   Rebalance Arith: size le
-- statement:
--   The sizes in the rebalancing. Here S, S', sc, sc' and Stot are natural numbers tied only by the
--   hypotheses: S' ≤ S + c₁(sc+P+B)^{c₁}, sc' ≤ c₁(sc+P) and Stot ≤ c₁(sc+P+B)^{c₁} + S' +
--   A(sc'+B'+β)^A. Then Stot exceeds S by at most a polynomial in sc + P + B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/RebalanceArith.lean#L36-L61
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Math/RebalanceArith.lean#L36-L61

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Definitions.Def_StepMachines_Math_RebalanceArith
set_option autoImplicit false
section
open Groundwork Groundwork.RebalanceArith

theorem Groundwork.RebalanceArith.size_le {K g : ℕ} (A c₁ d : ℕ) (hK : 2 ≤ K) (hKg : K ≤ g) :
    ∃ A' : ℕ, ∀ P B U β B' S S' sc sc' Stot : ℕ, 1 ≤ P → U ≤ g * P → K ^ 3 * β ≤ K ^ 3 + K * U + g * P →
      B' ≤ d * (P + B) → S' ≤ S + c₁ * (sc + P + B) ^ c₁ → sc' ≤ c₁ * (sc + P) →
      Stot ≤ c₁ * (sc + P + B) ^ c₁ + S' + A * (sc' + B' + β) ^ A → Stot ≤ S + A' * (sc + P + B) ^ A' := by sorry
