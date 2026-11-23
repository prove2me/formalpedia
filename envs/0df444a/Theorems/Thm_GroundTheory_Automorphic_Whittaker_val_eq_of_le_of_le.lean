-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_val_eq_of_le_of_le
-- name    : GroundTheory.Automorphic.Whittaker.val_eq_of_le_of_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:35.688794+00:00
-- url     : https://prove2.me/theorems/ac803fe8-c7bc-4e34-9cff-057679c71701
-- title:
--   Whittaker: val eq of le of le
-- statement:
--   The Whittaker construction uses the val eq of le of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L11-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerRelevance.lean#L11-L54

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

theorem GroundTheory.Automorphic.Whittaker.val_eq_of_le_of_le
    (hB : ∀ i j : Fin n, i < j → (w j).val = (w i).val + 1 → j.val = i.val + 1) :
    ∀ (g : ℕ) (z y : Fin n), (w y).val = (w z).val + g → z ≤ y →
      ∀ x : Fin n, z ≤ x → x ≤ y → (w x).val = (w z).val + (x.val - z.val) := by sorry
