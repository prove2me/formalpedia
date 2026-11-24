-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isPullback
-- name    : GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:41:23.037723+00:00
-- url     : https://prove2.me/theorems/a5a6eb75-c47c-40ce-8aee-5b7a4ccf685a
-- title:
--   Proper Functions: is Iso app Top of is Pullback
-- statement:
--   The Proper Functions construction uses the is Iso app Top of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L106-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L106-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TensorProduct Opposite
universe u
open GlobalTheory
open GlobalTheory.ProperFunctions
variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}

theorem GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [QuasiCompact p] [QuasiSeparated p] [IsIso p.appTop] : IsIso q.appTop := by sorry
