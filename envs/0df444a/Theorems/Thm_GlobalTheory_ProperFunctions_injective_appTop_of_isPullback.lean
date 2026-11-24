-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_injective_appTop_of_isPullback
-- name    : GlobalTheory.ProperFunctions.injective_appTop_of_isPullback
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:20.524209+00:00
-- url     : https://prove2.me/theorems/07efd4ac-fad2-4089-bd83-0667a8bf7089
-- title:
--   Proper Functions: injective app Top of is Pullback
-- statement:
--   The Proper Functions construction uses the injective app Top of is Pullback property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L143-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L143-L152

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

theorem GlobalTheory.ProperFunctions.injective_appTop_of_isPullback (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat p]
    (hf : Function.Injective f.appTop) : Function.Injective g.appTop := by sorry
