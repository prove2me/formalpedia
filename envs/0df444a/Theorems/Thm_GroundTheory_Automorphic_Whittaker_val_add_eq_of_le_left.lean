-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_add_eq_of_le_left
-- name    : GroundTheory.Automorphic.Whittaker.val_add_eq_of_le_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:31.540591+00:00
-- url     : https://prove2.me/theorems/9ff1e9ba-08fa-45c6-97ee-ad83376b1402
-- title:
--   Whittaker: val add eq of le left
-- statement:
--   The Whittaker construction uses the val add eq of le left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L83-L112
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L83-L112

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

theorem GroundTheory.Automorphic.Whittaker.val_add_eq_of_le_left
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) (b x : Fin n)
    (hxb : x ≤ b) (hx : b.val ≤ x.val + #(univ.filter fun y : Fin n => y < b ∧ w y < w b)) :
    (w x).val + (b.val - x.val) = (w b).val := by sorry
