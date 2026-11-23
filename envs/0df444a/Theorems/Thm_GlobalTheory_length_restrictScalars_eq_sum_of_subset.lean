-- Prove2me | Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_of_subset
-- name    : GlobalTheory.length_restrictScalars_eq_sum_of_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:47.710815+00:00
-- url     : https://prove2.me/theorems/378651d8-bff2-4013-8b9d-2b25d51098d4
-- title:
--   Global Theory: length restrict Scalars eq sum of subset
-- statement:
--   The Global Theory construction uses the length restrict Scalars eq sum of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L149-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L149-L184

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_LengthRestrictScalarsEqSumInertiaDegOfSubset
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
variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem GlobalTheory.length_restrictScalars_eq_sum_of_subset {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [iR : Module R X] [iT : IsScalarTower R S X]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0) :
    Module.length R X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * Module.length R (S ⧸ n.asIdeal) := by sorry
