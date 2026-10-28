-- Prove2me | Theorems.Thm_MarkovProcess_mem_image_val_iff
-- name    : MarkovProcess.mem_image_val_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T07:40:12.501989+00:00
-- url     : https://prove2.me/theorems/51a46ae4-e151-4796-a147-b5cd262ca2ee
-- title:
--   Characterisation of subtype image membership
-- statement:
--   The original theorem and complete proof from Scott Armstrong's MarkovProcess, commit 1f8060caa137731fa08029592019eeaf9d997fe5 (Apache-2.0). Characterisation of subtype image membership. Source: MarkovProcess/Killed/KillAtExit.lean, lines 37–42.

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib
open MeasureTheory
variable {alpha : Type*} (U : Set alpha)

theorem MarkovProcess.mem_image_val_iff {C : Set U} {y : alpha} (hy : y ∈ U) :
    y ∈ Subtype.val '' C ↔ (⟨y, hy⟩ : U) ∈ C := by sorry
