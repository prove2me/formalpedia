-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_isClosed_setOf_forall_llRank_le
-- name    : GroundTheory.Automorphic.Whittaker.isClosed_setOf_forall_llRank_le
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:05.663798+00:00
-- url     : https://prove2.me/theorems/c3e56141-e5e7-42c4-8186-19c4457f767b
-- title:
--   Whittaker: is Closed set Of forall ll Rank le
-- statement:
--   The Whittaker construction uses the is Closed set Of forall ll Rank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L76-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L76-L85

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

theorem GroundTheory.Automorphic.Whittaker.isClosed_setOf_forall_llRank_le (r : Fin n → Fin n → ℕ) :
    IsClosed {g : GL (Fin n) F | ∀ i j, llRank i j g ≤ r i j} := by sorry
