-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_termVal_pair
-- name    : Groundwork.Prog.NetE.termVal_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:53.478408+00:00
-- url     : https://prove2.me/theorems/c073773e-a1c4-4952-aec9-d794a55cfc54
-- title:
--   Net E: term Val pair
-- statement:
--   The factor number a*g + b.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L243-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L243-L259

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetVal
set_option autoImplicit false
section
open Groundwork
open Finset
open Groundwork.Prog Groundwork.Prog.NetE
variable {C : Type} {K g : ℕ} (Np : PNet C)

theorem Groundwork.Prog.NetE.termVal_pair {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x : ℕ) (q : IQ) (y : ℕ) (a b : Fin g) :
    termVal K g Np N ((((c, x), q), y), a.val * g + b.val) =
      if col K x a ≠ q.1 ∨ (col K x b = q.1 ∧ b < a) then 1
      else if a = b then N.W a (zA K g Np (((c, x), q), y) a)
      else if col K x b = q.1 then N.Ψ a b (zA K g Np (((c, x), q), y) a) (zA K g Np (((c, x), q), y) b)
      else N.f a b (zA K g Np (((c, x), q), y) a) (labOf K g Np ((c, x), q) a b) := by sorry
