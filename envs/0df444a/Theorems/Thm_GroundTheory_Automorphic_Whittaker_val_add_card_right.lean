-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_add_card_right
-- name    : GroundTheory.Automorphic.Whittaker.val_add_card_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:41.799572+00:00
-- url     : https://prove2.me/theorems/7034eb2b-e1e4-41cd-bc0c-ee4a44b6ed52
-- title:
--   Whittaker: val add card right
-- statement:
--   The Whittaker construction uses the val add card right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L121-L144
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L121-L144

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

theorem GroundTheory.Automorphic.Whittaker.val_add_card_right (w : Equiv.Perm (Fin n)) (b : Fin n) :
    (w b).val + #(univ.filter fun y : Fin n => b < y ∧ w b < w y) =
      #(univ.filter fun y : Fin n => y < b ∧ w y < w b) + (n - 1 - b.val) := by sorry
