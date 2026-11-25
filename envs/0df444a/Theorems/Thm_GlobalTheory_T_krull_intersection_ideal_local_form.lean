-- Prove2me | Theorems.Thm_GlobalTheory_T_krull_intersection_ideal_local_form
-- name    : GlobalTheory.T.krull_intersection_ideal_local_form
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:34:48.862086+00:00
-- url     : https://prove2.me/theorems/b890d8bc-aedc-47be-95c1-5a0e9596d27b
-- title:
--   T: krull intersection ideal local form
-- statement:
--   The T construction uses the krull intersection ideal local form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullIntersectionIdealLocalFormStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/KrullIntersectionIdealLocalFormStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullIntersectionIdealLocalForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullIntersectionIdealLocalFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.krull_intersection_ideal_local_form : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B), (∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) → ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by sorry
