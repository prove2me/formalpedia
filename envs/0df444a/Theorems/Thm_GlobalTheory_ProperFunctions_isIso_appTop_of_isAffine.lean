-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isAffine
-- name    : GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:37:33.579795+00:00
-- url     : https://prove2.me/theorems/f9341176-643a-4eb7-873b-9e7eb2536210
-- title:
--   Proper Functions: is Iso app Top of is Affine
-- statement:
--   The Proper Functions construction uses the is Iso app Top of is Affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L507-L517
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L507-L517

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

theorem GlobalTheory.ProperFunctions.isIso_appTop_of_isAffine (p : X ⟶ S) [IsAffine S] [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [LocallyOfFiniteType p] [GeometricallyIntegral p] :
    IsIso p.appTop := by sorry
