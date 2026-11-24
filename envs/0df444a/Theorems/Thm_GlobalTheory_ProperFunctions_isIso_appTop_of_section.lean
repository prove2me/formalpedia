-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_section
-- name    : GlobalTheory.ProperFunctions.isIso_appTop_of_section
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:22.643752+00:00
-- url     : https://prove2.me/theorems/a9d0c517-cbf2-436a-a262-b2d72fbb6ad4
-- title:
--   Proper Functions: is Iso app Top of section
-- statement:
--   The Proper Functions construction uses the is Iso app Top of section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L498-L505
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L498-L505

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

theorem GlobalTheory.ProperFunctions.isIso_appTop_of_section (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [GeometricallyIntegral p] {e : S ⟶ X} (he : e ≫ p = 𝟙 S) :
    IsIso p.appTop := by sorry
