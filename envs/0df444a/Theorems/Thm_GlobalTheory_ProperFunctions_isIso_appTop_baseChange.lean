-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_baseChange
-- name    : GlobalTheory.ProperFunctions.isIso_appTop_baseChange
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:30.494034+00:00
-- url     : https://prove2.me/theorems/01eb57cb-a3a6-437f-a656-b25ee071a9c4
-- title:
--   Proper Functions: is Iso app Top base Change
-- statement:
--   The Proper Functions construction uses the is Iso app Top base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L636-L662
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L636-L662

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
variable {X Y S T : Scheme.{u}}

theorem GlobalTheory.ProperFunctions.isIso_appTop_baseChange {p : X ⟶ S} {f : T ⟶ S} {g : Y ⟶ X} {q : Y ⟶ T}
    (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [IsLocallyNoetherian S] [Flat p]
    [IsProper p] [GeometricallyIntegral p] : IsIso q.appTop := by sorry
