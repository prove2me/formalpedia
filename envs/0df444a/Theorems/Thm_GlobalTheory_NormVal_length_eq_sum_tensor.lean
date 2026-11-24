-- Prove2me | Theorems.Thm_GlobalTheory_NormVal_length_eq_sum_tensor
-- name    : GlobalTheory.NormVal.length_eq_sum_tensor
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T18:35:58.47533+00:00
-- url     : https://prove2.me/theorems/84f68b46-1ed6-4c9b-8b8a-ce62e4eb3dc8
-- title:
--   Norm Val: length eq sum tensor
-- statement:
--   The Norm Val construction uses the length eq sum tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L171-L199
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L171-L199

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsDiscreteValuationRingLocalizationOfIsDedekindD
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IsDiscreteValuationRing IsLocalRing Module TensorProduct
open GlobalTheory.NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [Algebra R S]
  [Module.Finite R S]
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]

theorem GlobalTheory.NormVal.length_eq_sum_tensor {X : Type*} [AddCommGroup X] [Module S X] (hX : IsFiniteLength S X) :
    ∀ [Module R X] [IsScalarTower R S X], Module.length R X =
      ∑ n : MaximalSpectrum S, Module.length (A n) (A n ⊗[S] X) * n.asIdeal.inertiaDeg R := by sorry
