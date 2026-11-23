-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_eq_of_le_right
-- name    : GroundTheory.Automorphic.Whittaker.val_eq_of_le_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:46.841328+00:00
-- url     : https://prove2.me/theorems/5dfa7258-5906-48bd-8ab1-4eb4ab588380
-- title:
--   Whittaker: val eq of le right
-- statement:
--   The Whittaker construction uses the val eq of le right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L56-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L56-L81

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

theorem GroundTheory.Automorphic.Whittaker.val_eq_of_le_right
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hbx : b ≤ x) (hx : x.val ≤ b.val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y)) :
    (w x).val = (w b).val + (x.val - b.val) := by sorry
