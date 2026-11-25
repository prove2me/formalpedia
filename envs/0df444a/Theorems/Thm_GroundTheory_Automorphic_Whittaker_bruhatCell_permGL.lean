-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_permGL
-- name    : GroundTheory.Automorphic.Whittaker.bruhatCell_permGL
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:54:07.683432+00:00
-- url     : https://prove2.me/theorems/d8e19ff7-0388-5553-ab90-baed1da01ef9
-- title:
--   Whittaker: bruhat Cell perm GL
-- statement:
--   The Whittaker construction uses the bruhat Cell perm GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L297-L298
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L297-L298

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

theorem GroundTheory.Automorphic.Whittaker.bruhatCell_permGL (w : Equiv.Perm (Fin n)) : bruhatCell (permGL F w) = w := by sorry
