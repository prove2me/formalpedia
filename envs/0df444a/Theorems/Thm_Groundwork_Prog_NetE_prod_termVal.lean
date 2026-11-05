-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_prod_termVal
-- name    : Groundwork.Prog.NetE.prod_termVal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:15:10.849217+00:00
-- url     : https://prove2.me/theorems/4df935be-06d7-4c7a-b4b1-dde0b92b8e64
-- title:
--   Net E: prod term Val
-- statement:
--   The product of the factors, regrouped: weights, inner interactions, factors towards the other
--   classes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L279-L332
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetVal.lean#L279-L332

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

theorem Groundwork.Prog.NetE.prod_termVal (hK : 0 < K) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {t S : ℕ}
    (hN : Np.Presents c N t S) (x : ℕ) (G : Fin K) (θ : Fin K → List Bool) (y : ℕ) (Z : Fin g → List Bool)
    (hZ : ∀ a : Fin g, Z a = zA K g Np (((c, x), (G.val, List.ofFn θ)), y) a) :
    ∏ i ∈ range (g * g), termVal K g Np N ((((c, x), (G.val, List.ofFn θ)), y), i) =
      ((∏ a with chi hK x a = G, N.W a (Z a)) *
        ∏ p ∈ pairs (Fin g) with chi hK x p.1 = G ∧ chi hK x p.2 = G, N.Ψ p.1 p.2 (Z p.1) (Z p.2)) *
      ∏ G' ∈ univ.erase G, ∏ p : Fin g × Fin g with chi hK x p.1 = G ∧ chi hK x p.2 = G',
        N.f p.1 p.2 (Z p.1) (mdec K g Np c x (min G G') (max G G') (θ G') (if G < G' then p else p.swap)) := by sorry
