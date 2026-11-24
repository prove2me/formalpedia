-- Prove2me | Theorems.Thm_GlobalTheory_exists_lift_to_complete_dvr_of_finite
-- name    : GlobalTheory.exists_lift_to_complete_dvr_of_finite
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:34:05.714567+00:00
-- url     : https://prove2.me/theorems/ac6d8cf3-4318-45f2-bfdb-a5cdfe856047
-- title:
--   Global Theory: exists lift to complete dvr of finite
-- statement:
--   The Global Theory construction uses the exists lift to complete dvr of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftToCompleteDvrOfFinite.lean#L7-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLiftToCompleteDvrOfFinite.lean#L7-L79

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftToCompleteDvrOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory

theorem GlobalTheory.exists_lift_to_complete_dvr_of_finite : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by sorry
