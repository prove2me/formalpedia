-- Prove2me | Theorems.Thm_GlobalTheory_henselian_and_union_of_isIntegral_complete
-- name    : GlobalTheory.henselian_and_union_of_isIntegral_complete
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:55:38.336692+00:00
-- url     : https://prove2.me/theorems/c7061a4b-fda6-4a1a-8324-e30204dc2df5
-- title:
--   Global Theory: henselian and union of is Integral complete
-- statement:
--   The Global Theory construction uses the henselian and union of is Integral complete property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HenselianIUnionCompleteOfIntegralOverCompleteDvr.lean#L84-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HenselianIUnionCompleteOfIntegralOverCompleteDvr.lean#L84-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HenselianIUnionCompleteOfIntegralOverCompleteDvr
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.henselian_and_union_of_isIntegral_complete :
    ∀ (W R : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
      [IsAdicComplete (IsLocalRing.maximalIdeal W) W] [CharZero W] [CommRing R] [IsDomain R]
      [IsDiscreteValuationRing R] [Algebra W R], Function.Injective (algebraMap W R) →
      Algebra.IsIntegral W R → IsLocalHom (algebraMap W R) ∧ HenselianLocalRing R ∧
      ∀ s : Finset R, ∃ (W' : Subalgebra W R) (_ : IsDiscreteValuationRing W'),
        (↑s : Set R) ⊆ W' ∧ IsAdicComplete (IsLocalRing.maximalIdeal W') W' ∧
        Module.Finite W W' ∧ IsLocalHom W'.val.toRingHom := by sorry
