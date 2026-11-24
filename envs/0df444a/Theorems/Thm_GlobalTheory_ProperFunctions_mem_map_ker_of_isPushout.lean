-- Prove2me | Theorems.Thm_GlobalTheory_ProperFunctions_mem_map_ker_of_isPushout
-- name    : GlobalTheory.ProperFunctions.mem_map_ker_of_isPushout
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:56:23.3219+00:00
-- url     : https://prove2.me/theorems/bc9db7f0-2156-4291-a69f-21250ae64c89
-- title:
--   Proper Functions: mem map ker of is Pushout
-- statement:
--   The Proper Functions construction uses the mem map ker of is Pushout property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L60-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsIsoAppTopOfIsPullbackOfSurjective.lean#L60-L70

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

theorem GlobalTheory.ProperFunctions.mem_map_ker_of_isPushout {R A K P : CommRingCat.{u}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hφ : φ.hom.Flat) (x : A)
    (hx : inl x = 0) : x ∈ (RingHom.ker ψ.hom).map φ.hom := by sorry
