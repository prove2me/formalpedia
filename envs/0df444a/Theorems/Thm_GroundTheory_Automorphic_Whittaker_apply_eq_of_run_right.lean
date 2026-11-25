-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_apply_eq_of_run_right
-- name    : GroundTheory.Automorphic.Whittaker.apply_eq_of_run_right
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:34:52.092027+00:00
-- url     : https://prove2.me/theorems/2324153d-a8db-40ed-a211-13c9902077ea
-- title:
--   Whittaker: apply eq of run right
-- statement:
--   The Whittaker construction uses the apply eq of run right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L164-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L164-L194

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Finset
variable {n : ℕ} {w : Equiv.Perm (Fin n)}

theorem GroundTheory.Automorphic.Whittaker.apply_eq_of_run_right {α : Type*} (t : Fin n → α)
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1)
    (ht : ∀ (i : Fin n) (h : i.val + 1 < n), w i < w ⟨i.val + 1, h⟩ →
      t (w i) = t (w ⟨i.val + 1, h⟩))
    (b : Fin n) :
    ∀ k : ℕ, ∀ x : Fin n, x.val = b.val + k →
      k ≤ #(univ.filter fun y : Fin n => b < y ∧ w b < w y) → t (w x) = t (w b) := by sorry
