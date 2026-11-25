-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_mem_doubleCoset_bruhatCell
-- name    : GroundTheory.Automorphic.Whittaker.mem_doubleCoset_bruhatCell
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:29:44.997787+00:00
-- url     : https://prove2.me/theorems/6f4dfe04-7e34-4df1-8118-758d36ec7fd5
-- title:
--   Whittaker: mem double Coset bruhat Cell
-- statement:
--   The Whittaker construction uses the mem double Coset bruhat Cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L285-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L285-L287

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

theorem GroundTheory.Automorphic.Whittaker.mem_doubleCoset_bruhatCell (g : GL (Fin n) F) :
    g ∈ doubleCoset (permGL F (bruhatCell g)) (borel n F) (borel n F) := by sorry
