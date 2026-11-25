-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_bruhatCell_mul_mul
-- name    : GroundTheory.Automorphic.Whittaker.bruhatCell_mul_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:40:54.574207+00:00
-- url     : https://prove2.me/theorems/dcc2d46b-0b96-41b3-9825-6166bb009f07
-- title:
--   Whittaker: bruhat Cell mul mul
-- statement:
--   The Whittaker construction uses the bruhat Cell mul mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L300-L306
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L300-L306

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

theorem GroundTheory.Automorphic.Whittaker.bruhatCell_mul_mul {a b : GL (Fin n) F} (ha : a ∈ borel n F) (hb : b ∈ borel n F)
    (g : GL (Fin n) F) : bruhatCell (a * g * b) = bruhatCell g := by sorry
