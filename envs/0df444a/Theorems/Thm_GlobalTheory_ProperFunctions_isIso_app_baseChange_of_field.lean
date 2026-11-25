-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app_baseChange_of_field
-- name    : GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:15:42.626923+00:00
-- url     : https://prove2.me/theorems/3d423838-8a0a-5910-a8b5-5b97ca9d7b36
-- title:
--   Proper Functions: is Iso app base Change of field
-- statement:
--   The Proper Functions construction uses the is Iso app base Change of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L446-L452
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L446-L452

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

theorem GlobalTheory.ProperFunctions.isIso_app_baseChange_of_field {k : Type u} [Field k] {p : X ⟶ Spec (.of k)}
    {f : T ⟶ Spec (.of k)} {g : Y ⟶ X} {q : Y ⟶ T} (H : IsPullback g q p f)
    [GeometricallyIntegral p] [UniversallyClosed p] [QuasiSeparated p] (U : T.Opens) :
    IsIso (q.app U) := by sorry
