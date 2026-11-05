-- Prove2me | Theorems.Thm_Groundwork_TM_Frag_ren_runs
-- name    : Groundwork.TM.Frag.ren_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:11:39.515488+00:00
-- url     : https://prove2.me/theorems/ed529e0e-90af-4e97-b2e6-07e338384351
-- title:
--   Frag: ren runs
-- statement:
--   If S and S' agree with T and T' along φ and with each other outside the image of φ, a run of P
--   from T to T' becomes a
--   run of `P.ren φ` from S to S' with the same number of steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Rename.lean#L104-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/TM/Rename.lean#L104-L107

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

theorem Groundwork.TM.Frag.ren_runs (hφ : Function.Injective φ) {P : Frag (fun _ : K₁ => A) σ} {v : σ} {T T' : K₁ → List A} {n : ℕ}
    (h : P.Runs v T n T') {S S' : K₂ → List A} (hS : ∀ k, S (φ k) = T k) (hS' : ∀ k, S' (φ k) = T' k)
    (ho : ∀ k, (∀ a, φ a ≠ k) → S' k = S k) : (P.ren φ).Runs v S n S' := by sorry
