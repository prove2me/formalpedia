-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_mergedM_runs
-- name    : Groundwork.Prog.NetE.mergedM_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:38.658081+00:00
-- url     : https://prove2.me/theorems/14c071af-7c5d-4424-81e8-5760645e1d98
-- title:
--   Net E: merged M runs
-- statement:
--   `mergedM` computes one entry of the tensor of class G of the merged instance, by brute force
--   over the states of the
--   members of G. Here x is a colouring in which any two classes share at most β label bits (β is the
--   length of the labels in
--   the query) and every class has at most m members.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L287-L346
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L287-L346

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
set_option autoImplicit false
section
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open Finset Stepped
variable {C : Type} (K g : ℕ) (Np : PNet C)
variable [HasSize C]

theorem Groundwork.Prog.NetE.mergedM_runs {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
    (hN : Np.Presents c N t S) (hS : N.Sized P B) (ht : 1 ≤ t) (x β m : ℕ)
    (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β)
    (G : Fin K) (θ : Fin K → List Bool) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    (mergedM K g Np).Runs ((c, x), (G.val, List.ofFn θ))
      (2 ^ (P * m) * (g * g * (2 ^ P * (2 * t + 3) + 2) + 1))
      (S + 4 * (size c + size x + size K + K * (2 * β + 2)) + 5 * (P * m) + 2 * (B * (g * g)) + 3 * size (g * g)
        + 3 * P + 3 * B + 28)
      (mergedVal K g Np N ((c, x), (G.val, List.ofFn θ))) := by sorry
