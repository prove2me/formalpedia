-- Prove2me | Theorems.Thm_Groundwork_Prog_all_pairs_iff
-- name    : Groundwork.Prog.all_pairs_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:25.447224+00:00
-- url     : https://prove2.me/theorems/40b0c948-8f6b-44f2-ae8c-ac8faed18a82
-- title:
--   Prog: all pairs iff
-- statement:
--   The double loop over i' > i, as a test on the pairs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridCount.lean#L19-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/GridCount.lean#L19-L30

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_StepMachines_Prog_GridCount
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset

theorem Groundwork.Prog.all_pairs_iff (g : ℕ) (p : ℕ → ℕ → Bool) :
    ((List.range g).all fun i => (List.range g).all fun i' => decide (i' ≤ i) || p i i') = true ↔
      ∀ q ∈ pairs (Fin g), p q.1 q.2 = true := by sorry
