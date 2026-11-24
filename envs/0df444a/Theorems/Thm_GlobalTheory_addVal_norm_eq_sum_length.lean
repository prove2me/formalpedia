-- Prove2me | Theorems.Thm_GlobalTheory_addVal_norm_eq_sum_length
-- name    : GlobalTheory.addVal_norm_eq_sum_length
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:05:49.611507+00:00
-- url     : https://prove2.me/theorems/5a841513-06c6-446a-9db1-b84ca2e383e9
-- title:
--   Global Theory: add Val norm eq sum length
-- statement:
--   The Global Theory construction uses the add Val norm eq sum length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L245-L250
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/IsDiscreteValuationRingLocalizationOfIsDedekindD.lean#L245-L250

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
open NormVal
variable (R : Type*) {S : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]
variable [Fintype (MaximalSpectrum S)] (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)]
  [∀ n, Algebra S (A n)] [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]

theorem GlobalTheory.addVal_norm_eq_sum_length {x : S} (hx : x ∈ nonZeroDivisors S) :
    addVal R (Algebra.norm R x) = ∑ n : MaximalSpectrum S,
      Module.length (A n) (A n ⧸ Ideal.span {algebraMap S (A n) x}) * n.asIdeal.inertiaDeg R := by sorry
