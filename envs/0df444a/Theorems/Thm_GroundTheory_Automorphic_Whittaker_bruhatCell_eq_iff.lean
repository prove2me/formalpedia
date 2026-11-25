-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_eq_iff
-- name    : GroundTheory.Automorphic.Whittaker.bruhatCell_eq_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:45.892192+00:00
-- url     : https://prove2.me/theorems/4ad8f668-37c3-479d-964d-71bbb2393529
-- title:
--   Whittaker: bruhat Cell eq iff
-- statement:
--   The Whittaker construction uses the bruhat Cell eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L289-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L289-L295

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
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
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.Whittaker.bruhatCell_eq_iff {g : GL (Fin n) F} {w : Equiv.Perm (Fin n)} :
    bruhatCell g = w ↔ g ∈ doubleCoset (permGL F w) (borel n F) (borel n F) := by sorry
