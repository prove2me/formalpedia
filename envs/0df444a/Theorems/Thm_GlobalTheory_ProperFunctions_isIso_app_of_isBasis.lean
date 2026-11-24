-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_app_of_isBasis
-- name    : GlobalTheory.ProperFunctions.isIso_app_of_isBasis
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:56:17.461515+00:00
-- url     : https://prove2.me/theorems/9beae4e2-0fd4-408c-8f9b-77ea13b0ff32
-- title:
--   Proper Functions: is Iso app of is Basis
-- statement:
--   The Proper Functions construction uses the is Iso app of is Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L421-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L421-L434

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

theorem GlobalTheory.ProperFunctions.isIso_app_of_isBasis (p : X ⟶ S) {ι : Type*} (B : ι → S.Opens)
    (hB : TopologicalSpace.Opens.IsBasis (Set.range B))
    (h : ∀ i, IsIso (p ∣_ B i).appTop) (U : S.Opens) : IsIso (p.app U) := by sorry
