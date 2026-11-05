-- Prove2me | Theorems.Thm_Groundwork_Prog_Count_all_links_iff
-- name    : Groundwork.Prog.Count.all_links_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:59:51.414201+00:00
-- url     : https://prove2.me/theorems/e4c8b07d-c77b-4b56-811c-2639d3fe3a22
-- title:
--   Count: all links iff
-- statement:
--   A condition on all links of two clusters, read on slots.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L225-L238
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/StepMachines/Prog/CountNet.lean#L225-L238

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_StepMachines_Prog_Spec
import Definitions.Def_StepMachines_Math_SatNet
import Definitions.Def_StepMachines_Prog_CountNet
set_option autoImplicit false
section
open Groundwork Groundwork.Prog
open Finset SatNet
open Groundwork.Prog.Count
variable {g μ k : ℕ} {φ : Fml}

theorem Groundwork.Prog.Count.all_links_iff (hg : 0 < g) (hm : φ.length ≤ g * mu g φ) (a b : Fin g) (P : ℕ → ℕ → Bool) :
    ((links g k φ a.val b.val).all fun p => P p.1 p.2) = true ↔
      ∀ s s' : Sl (mu g φ) k, Link φ (a, s) (b, s') → P (loc s) (loc s') = true := by sorry
