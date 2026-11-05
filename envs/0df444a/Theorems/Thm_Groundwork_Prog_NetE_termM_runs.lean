-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_termM_runs
-- name    : Groundwork.Prog.NetE.termM_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:14:40.026701+00:00
-- url     : https://prove2.me/theorems/7630eb24-372a-4d95-9578-2b4513150bba
-- title:
--   Net E: term M runs
-- statement:
--   One factor of the product in an entry of the merged tensor of class G. The index i < g * g codes
--   the pair of nodes
--   (i / g, i % g); the factor is 1, a weight W, an interaction Ψ inside the class (a sum over the
--   labels of the pair), or a
--   factor f towards a node of another class. It has absolute value at most 2 ^ B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L149-L258
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L149-L258

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
variable {K g Np} {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B t S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}
variable [HasSize C]

theorem Groundwork.Prog.NetE.termM_runs (hN : Np.Presents c N t S) (hS : N.Sized P B) (ht : 1 ≤ t)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β)
    (y : ℕ) {i : ℕ} (hi : i < g * g) :
    (termM K g Np).Runs ((((c, x), (G.val, List.ofFn θ)), y), i) (2 ^ P * (2 * t + 2))
      (2 * size ((((c, x), (G.val, List.ofFn θ)), y), i) + 3 * P + 3 * B + S + 12)
      (termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)) ∧
    (termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i)).natAbs ≤ 2 ^ B := by sorry
