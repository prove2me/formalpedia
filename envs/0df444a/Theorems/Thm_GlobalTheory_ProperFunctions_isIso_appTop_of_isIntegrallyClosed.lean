-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_appTop_of_isIntegrallyClosed
-- name    : GlobalTheory.ProperFunctions.isIso_appTop_of_isIntegrallyClosed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T18:56:20.586146+00:00
-- url     : https://prove2.me/theorems/aa699126-9c69-4af6-b6a7-3ceba086591c
-- title:
--   Proper Functions: is Iso app Top of is Integrally Closed
-- statement:
--   The Proper Functions construction uses the is Iso app Top of is Integrally Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L454-L496
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L454-L496

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

theorem GlobalTheory.ProperFunctions.isIso_appTop_of_isIntegrallyClosed {R K : Type u} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] {p : X ⟶ Spec (.of R)}
    {g : Y ⟶ X} {q : Y ⟶ Spec (.of K)}
    (H : IsPullback g q p (Spec.map (CommRingCat.ofHom (algebraMap R K))))
    [Flat p] [UniversallyClosed p] [GeometricallyIntegral q] : IsIso p.appTop := by sorry
