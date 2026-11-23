-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app
-- name    : GlobalTheory.ProperFunctions.isIso_app
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:42:47.218911+00:00
-- url     : https://prove2.me/theorems/3a631d8c-f9e6-42ce-bd82-454293668976
-- title:
--   Proper Functions: is Iso app
-- statement:
--   The Proper Functions construction uses the is Iso app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L519-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L519-L524

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

theorem GlobalTheory.ProperFunctions.isIso_app (p : X ⟶ S) [IsLocallyNoetherian S] [Flat p]
    [UniversallyClosed p] [LocallyOfFiniteType p] [GeometricallyIntegral p] (U : S.Opens) :
    IsIso (p.app U) := by sorry
