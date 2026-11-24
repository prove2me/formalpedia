-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isPullback_of_surjective
-- name    : GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback_of_surjective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:39:11.507148+00:00
-- url     : https://prove2.me/theorems/d1441a62-4aea-4465-80a8-5f1522a31b7b
-- title:
--   Proper Functions: is Iso app Top of is Pullback of surjective
-- statement:
--   The Proper Functions construction uses the is Iso app Top of is Pullback of surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L110-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L110-L126

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

theorem GlobalTheory.ProperFunctions.isIso_appTop_of_isPullback_of_surjective (H : IsPullback g q p f) [IsAffine S]
    [IsAffine T] [Flat f] [Surjective f] [QuasiCompact p] [IsIso q.appTop] : IsIso p.appTop := by sorry
