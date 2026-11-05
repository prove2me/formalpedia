-- Prove2me | Theorems.Thm_Groundwork_Prog_NetE_length_labOf
-- name    : Groundwork.Prog.NetE.length_labOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:58:50.391239+00:00
-- url     : https://prove2.me/theorems/8aa254a3-5d47-4c61-8daa-954ed64b7fb5
-- title:
--   Net E: length lab Of
-- statement:
--   The Net E construction uses the length lab Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L123-L140
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/NetRun.lean#L123-L140

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

theorem Groundwork.Prog.NetE.length_labOf (hN : Np.Presents c N t S) (hS : N.Sized P B)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β)
    {a b : ℕ} (ha : a ∈ members K g x G) (hb : b < g) (hc : col K x b ≠ G) :
    (labOf K g Np ((c, x), (G.val, List.ofFn θ)) a b).length = Np.cap c a b := by sorry
