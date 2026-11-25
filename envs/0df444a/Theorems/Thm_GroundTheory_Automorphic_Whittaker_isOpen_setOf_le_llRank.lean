-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isOpen_setOf_le_llRank
-- name    : GroundTheory.Automorphic.Whittaker.isOpen_setOf_le_llRank
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:29:12.115251+00:00
-- url     : https://prove2.me/theorems/acb5e310-b696-4f36-bca2-1c11ff400c54
-- title:
--   Whittaker: is Open set Of le ll Rank
-- statement:
--   The Whittaker construction uses the is Open set Of le ll Rank property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L54-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L54-L68

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

theorem GroundTheory.Automorphic.Whittaker.isOpen_setOf_le_llRank (i j : Fin n) (k : ℕ) :
    IsOpen {g : GL (Fin n) F | k ≤ llRank i j g} := by sorry
