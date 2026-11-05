-- Prove2me | Theorems.Thm_Groundwork_inTimeTM_of_machine
-- name    : Groundwork.inTimeTM_of_machine
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:34.007735+00:00
-- url     : https://prove2.me/theorems/cf4211f8-e728-4a5a-92d9-6e808caa8b40
-- title:
--   Groundwork: in Time TM of machine
-- statement:
--   Take a machine cut into polynomial-time steps that decides 3-SAT in at most c·2^{δn/2} steps,
--   with every state of size at
--   most c·(|input|+1)^c. It gives a Turing machine with finite alphabets that decides 3-SAT within
--   ⌊C·2^{δn}⌋ steps, which is
--   `InTimeTM δ`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/EndTM.lean#L55-L91
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/EndTM.lean#L55-L91

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_Host
import Definitions.Def_StepMachines_Prog_Decode
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Definitions.Def_ToTuring_Machine_EndTM
set_option autoImplicit false
section
open Groundwork
open Sat3 Turing
open scoped NNReal

theorem Groundwork.inTimeTM_of_machine {δ : ℝ≥0} (hδ : 0 < δ) (M : Stepped (List Bool) Bool) [IsPolyT M] (c : ℕ)
    (h : ∀ (n : ℕ) (φ : CNF n), Is3CNF φ →
      ∃ (T : ℕ) (b : Bool), M.Runs (enc φ) T (c * ((enc φ).length + 1) ^ c) b ∧
        (b = true ↔ Satisfiable φ) ∧ (T : ℝ) ≤ c * (2 : ℝ) ^ ((δ : ℝ) / 2 * n)) : InTimeTM δ := by sorry
