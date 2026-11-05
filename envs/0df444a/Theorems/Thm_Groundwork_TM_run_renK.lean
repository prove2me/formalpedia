-- Prove2me | Theorems.Thm_Groundwork_TM_run_renK
-- name    : Groundwork.TM.run_renK
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:37.738526+00:00
-- url     : https://prove2.me/theorems/0faa875e-2a1a-4170-8c89-3886ca767293
-- title:
--   TM: run ren K
-- statement:
--   Runs of a machine become runs of the renamed machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Rename.lean#L78-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Rename.lean#L78-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_TM_Frag
import Definitions.Def_ToTuring_TM_Rename
set_option autoImplicit false
section
section
open Groundwork Groundwork.TM
open Turing
variable {K₁ K₂ : Type} [DecidableEq K₁] [DecidableEq K₂] {A Λ σ : Type} (φ : K₁ → K₂)
variable {φ}

theorem Groundwork.TM.run_renK (hφ : Function.Injective φ) {M : Λ → TM2.Stmt (fun _ : K₁ => A) Λ σ} :
    ∀ {n : ℕ} {l l' : Option Λ} {v v' : σ} {T T' : K₁ → List A}, Run (TM2.step M) ⟨l, v, T⟩ n ⟨l', v', T'⟩ →
      ∀ {S S' : K₂ → List A}, (∀ k, S (φ k) = T k) → (∀ k, S' (φ k) = T' k) → (∀ k, (∀ a, φ a ≠ k) → S' k = S k) →
        Run (TM2.step fun l => renK φ (M l)) ⟨l, v, S⟩ n ⟨l', v', S'⟩
  := by sorry
