-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_goodB_iff
-- name    : Groundwork.Prog.NetE.goodB_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:31.575432+00:00
-- url     : https://prove2.me/theorems/3e2dcacc-782c-4d9d-93e8-a7767826f81d
-- title:
--   Net E: good B iff
-- statement:
--   What the test goodB of a colouring says: every class has fewer than 2g/K nodes, and two classes
--   share at most betaC
--   label bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L463-L482
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L463-L482

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
variable {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}

theorem Groundwork.Prog.NetE.goodB_iff (hK : 0 < K) (hN : Np.Presents c N t S) (x : ℕ) :
    goodB K g Np (c, x) = true ↔ (∀ G : Fin K, K * #{a : Fin g | chi hK x a = G} < 2 * g) ∧
      ∀ G G' : Fin K, G ≠ G' → (N.merge (chi hK x) [] []).c G G' ≤ betaC K g Np c := by sorry
