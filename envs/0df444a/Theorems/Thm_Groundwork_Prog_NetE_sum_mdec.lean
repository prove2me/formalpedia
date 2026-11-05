-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_sum_mdec
-- name    : Groundwork.Prog.NetE.sum_mdec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:22.086454+00:00
-- url     : https://prove2.me/theorems/09d88db3-c0c6-41ba-8aeb-a331d3d25bc2
-- title:
--   Net E: sum mdec
-- statement:
--   The Net E construction uses the sum mdec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L177-L215
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L177-L215

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

theorem Groundwork.Prog.NetE.sum_mdec (hK : 0 < K) (c : C) (x β : ℕ) (G G' : Fin K) (hβ : lbLen K g Np c x G G' ≤ β)
    (F : (Fin g × Fin g → List Bool) → ℤ) :
    ∑ θ ∈ mD K g Np c x β G G', F (mdec K g Np c x G G' θ) =
      ∑ t ∈ tuples (fun p : Fin g × Fin g => chi hK x p.1 = G ∧ chi hK x p.2 = G')
        (fun p => words (Np.cap c p.1.val p.2.val)) [], F t := by sorry
