-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_isIso_of_isPushout_of_faithfullyFlat
-- name    : GlobalTheory.ProperFunctions.isIso_of_isPushout_of_faithfullyFlat
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:56:24.008601+00:00
-- url     : https://prove2.me/theorems/e73ab65c-53d3-4e07-913b-f42844e8fcd9
-- title:
--   Proper Functions: is Iso of is Pushout of faithfully Flat
-- statement:
--   The Proper Functions construction uses the is Iso of is Pushout of faithfully Flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L72-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L72-L82

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

theorem GlobalTheory.ProperFunctions.isIso_of_isPushout_of_faithfullyFlat {R A K P : CommRingCat.{u}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hψ : ψ.hom.FaithfullyFlat)
    [IsIso inr] : IsIso φ := by sorry
