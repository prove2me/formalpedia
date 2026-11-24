-- Prove2me | Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_inertiaDeg_of_subset
-- name    : GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg_of_subset
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:05:56.011352+00:00
-- url     : https://prove2.me/theorems/cacf3637-76fd-4308-919c-51bd24a5c084
-- title:
--   Global Theory: length restrict Scalars eq sum inertia Deg of subset
-- statement:
--   The Global Theory construction uses the length restrict Scalars eq sum inertia Deg of subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L220-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L220-L235

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

theorem GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg_of_subset [IsLocalRing R] {X : Type*}
    [AddCommGroup X] [Module S X] (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X]
    (T : Finset (MaximalSpectrum S))
    (hT : ∀ n ∉ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) = 0)
    (hover : ∀ n ∈ T, n.asIdeal.LiesOver (maximalIdeal R))
    (hfin : ∀ n ∈ T, Module.Finite R (S ⧸ n.asIdeal)) :
    Module.length R X = ∑ n ∈ T, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞) := by sorry
