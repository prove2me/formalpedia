-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isOpen_setOf_forall_le_llRank
-- name    : GroundTheory.Automorphic.Whittaker.isOpen_setOf_forall_le_llRank
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:00.950032+00:00
-- url     : https://prove2.me/theorems/0408e4ce-271a-4f0d-aef5-a65d4355cfa0
-- title:
--   Whittaker: is Open set Of forall le ll Rank
-- statement:
--   The Whittaker construction uses the is Open set Of forall le ll Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L70-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L70-L74

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
variable [TopologicalSpace F] [IsTopologicalRing F] [T1Space F]

theorem GroundTheory.Automorphic.Whittaker.isOpen_setOf_forall_le_llRank (r : Fin n → Fin n → ℕ) :
    IsOpen {g : GL (Fin n) F | ∀ i j, r i j ≤ llRank i j g} := by sorry
