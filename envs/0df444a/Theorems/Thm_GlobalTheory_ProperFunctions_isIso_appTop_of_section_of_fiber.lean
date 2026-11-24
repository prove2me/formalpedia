-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_section_of_fiber
-- name    : GlobalTheory.ProperFunctions.isIso_appTop_of_section_of_fiber
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:56:12.870228+00:00
-- url     : https://prove2.me/theorems/cb390919-44f6-466d-94b0-8b69f558be9c
-- title:
--   Proper Functions: is Iso app Top of section of fiber
-- statement:
--   The Proper Functions construction uses the is Iso app Top of section of fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L392-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L392-L413

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
variable {X S : Scheme.{u}}

theorem GlobalTheory.ProperFunctions.isIso_appTop_of_section_of_fiber (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    (hq : ∀ s : S, Function.Surjective (p.fiberToSpecResidueField s).appTop)
    {e : S ⟶ X} (he : e ≫ p = 𝟙 S) : IsIso p.appTop := by sorry
