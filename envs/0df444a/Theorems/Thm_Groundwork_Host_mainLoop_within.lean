-- Prove2me | Theorems.Thm_Groundwork_Host_mainLoop_within
-- name    : Groundwork.Host.mainLoop_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:48:52.072174+00:00
-- url     : https://prove2.me/theorems/41022ce9-8c10-4cf6-afdd-0603771cd046
-- title:
--   Host: main Loop within
-- statement:
--   The loop, from a state that reaches the result b within t steps: at most t rounds, and the last
--   state is left on the
--   main stack.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L225-L245
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/machines/ToTuring/Machine/Host.lean#L225-L245

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_Machine_Lift
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_ToTuring_Machine_Host
set_option autoImplicit false
section
section
open Groundwork
open TM Turing
open Groundwork.Host
variable {M : Stepped (List Bool) Bool}
variable [Enc M.σ]
variable {Ps Po : Fr} {tS tO : ℕ → ℕ}
  (hS : ∀ (s : M.σ) (M' A B N : List Sym),
    Ps.Within (st (wd s ++ M') A B N) (tS (len s)) (st (wd (M.step s) ++ M') A B N))
  (hO : ∀ (s : M.σ) (M' A B N : List Sym),
    Po.Within (st (wd s ++ M') A B N) (tO (len s)) (st (wd (M.out s) ++ M') A B N))
include hS hO

theorem Groundwork.Host.mainLoop_within (mS : Monotone tS) (mO : Monotone tO) {S L : ℕ} (hL : ∀ s : M.σ, size s ≤ S → len s ≤ L) {b : Bool}
    {s : M.σ} {t : ℕ} (h : M.Reaches S b s t) :
    ∃ s' : M.σ, size s' ≤ S ∧ Frag.Within (mainLoop Ps Po) (withIO [] (st (wd (M.out s) ++ (wd s ++ [])) [] [] []))
      (t * (1 + (tS L + (3 * L + 3 + tO L))) + 1) (withIO [b] (st (wd s' ++ []) [] [] [])) := by sorry
