-- Prove2me | Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_inertiaDeg
-- name    : GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:56.198738+00:00
-- url     : https://prove2.me/theorems/d400b891-298f-4a16-abbc-d870492214f6
-- title:
--   Global Theory: length restrict Scalars eq sum inertia Deg
-- statement:
--   The Global Theory construction uses the length restrict Scalars eq sum inertia Deg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L261-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L261-L267

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
variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]

theorem GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    Module.length R X = ∑ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * (n.asIdeal.inertiaDeg R : ℕ∞) := by sorry
