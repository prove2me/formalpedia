-- Prove2me | Theorems.Thm_Groundwork_exists_tm
-- name    : Groundwork.exists_tm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:54:35.417321+00:00
-- url     : https://prove2.me/theorems/9c984e4c-aa79-4685-a71f-b35704a4a0f2
-- title:
--   Groundwork: exists tm
-- statement:
--   A stepped computation on bit strings with polynomial-time init, step and out runs on one of
--   Mathlib's multi-stack
--   machines with finite alphabets. If it ends on x within T steps with states of size at most (|x| + 2)^d,
--   the machine takes
--   at most c · (T + 1) · (|x| + 1)^c steps, where c depends on the computation and d only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L305-L355
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L305-L355

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Host

theorem Groundwork.exists_tm (M : Stepped (List Bool) Bool) [IsPolyT M] (d : ℕ) :
    ∃ (N : TM2ComputableAux Bool Bool) (c : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ (x : List Bool) (T S : ℕ) (b : Bool), M.Runs x T S b → S ≤ (x.length + 2) ^ d →
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun) (some ([b].map N.outputAlphabet.invFun))
          (c * (T + 1) * (x.length + 1) ^ c)) := by sorry
