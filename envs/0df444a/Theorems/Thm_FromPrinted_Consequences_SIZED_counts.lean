-- Prove2me | Theorems.Thm_FromPrinted_Consequences_SIZED_counts
-- name    : FromPrinted.Consequences.SIZED_counts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:23:19.444165+00:00
-- url     : https://prove2.me/theorems/1ad6eb1b-b9b8-4218-b7e0-181d0d6e00bb
-- title:
--   Consequences: SIZED counts
-- statement:
--   For every width w and δ > 0 there are ℓ, τ such that `SIZED w ℓ τ` has polynomial-time steps and
--   returns, on (n in unary, s, ψ) for s ≤ n and ψ of width at most w on x₀ … xₙ₋₁, the number of
--   satisfying assignments of ψ with exactly s true variables, within c·2^{δn} steps, on states of size
--   at most c·(n + number of clauses + 2)^c.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sets.lean#L47-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/FromPrinted/Sets.lean#L47-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_FromPrinted_GraphDefs
import Definitions.Def_FromPrinted_Count
import Definitions.Def_Consequences_Sets
import Definitions.Def_SizeCircuit_Main
import Definitions.Def_Complement_Readers
import Definitions.Def_Eight_ViaGrouping_CorGraph
import Definitions.Def_GraphProblems_Read
import Definitions.Def_GraphProblems_Sets
import Definitions.Def_GraphProblems_Cert
import Definitions.Def_GraphProblems_SetTM
import Mathlib.Tactic
import Definitions.Def_FromPrinted_Sets
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Consequences
open FromPrinted FromPrinted.Consequences
open Groundwork Groundwork.Prog CountKSat GraphProblems Paper Eight Eight.ViaGrouping FromPrinted.SplitCount SizeCircuit Complement

theorem FromPrinted.Consequences.SIZED_counts (w : ℕ) {δ : ℝ} (hδ : 0 < δ) : ∃ ℓ τ : ℕ, PolyTimeSteps (SIZED w ℓ τ) ∧ ∃ c : ℕ, ∀ (n s : ℕ) (ψ : Fml), s ≤ n → Shaped w n ψ →
    ∃ T : ℕ, (SIZED w ℓ τ).Runs (List.replicate n (), s, ψ) T (c * (n + ψ.length + 2) ^ c) (cntS n s ψ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ (δ * n) := by sorry
