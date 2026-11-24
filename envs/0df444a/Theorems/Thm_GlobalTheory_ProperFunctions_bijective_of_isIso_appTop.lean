-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_bijective_of_isIso_appTop
-- name    : GlobalTheory.ProperFunctions.bijective_of_isIso_appTop
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:16.245697+00:00
-- url     : https://prove2.me/theorems/ea521e3a-48f9-4299-b3a1-9e5a8d487620
-- title:
--   Proper Functions: bijective of is Iso app Top
-- statement:
--   The Proper Functions construction uses the bijective of is Iso app Top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L664-L666
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L664-L666

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

theorem GlobalTheory.ProperFunctions.bijective_of_isIso_appTop {R : CommRingCat.{u}} (p : X ⟶ Spec R) [IsIso p.appTop] :
    Function.Bijective ((Scheme.ΓSpecIso R).inv ≫ p.appTop) := by sorry
