-- Prove2me | Theorems.Thm_GlobalTheory_length_restrictScalars_eq_sum_inertiaDeg_of_isLocalizedModule
-- name    : GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg_of_isLocalizedModule
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:05:49.440655+00:00
-- url     : https://prove2.me/theorems/043fc0a4-6bec-439b-a353-1ad1db62e1ec
-- title:
--   Global Theory: length restrict Scalars eq sum inertia Deg of is Localized Module
-- statement:
--   The Global Theory construction uses the length restrict Scalars eq sum inertia Deg of is Localized Module property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L269-L281
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L269-L281

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

theorem GlobalTheory.length_restrictScalars_eq_sum_inertiaDeg_of_isLocalizedModule [Module.Finite R S]
    [Fintype (MaximalSpectrum S)] {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X]
    (A : MaximalSpectrum S → Type*) [∀ n, CommRing (A n)] [∀ n, Algebra S (A n)]
    [∀ n, IsLocalization.AtPrime (A n) n.asIdeal]
    (Y : MaximalSpectrum S → Type*) [∀ n, AddCommGroup (Y n)] [∀ n, Module S (Y n)]
    [∀ n, Module (A n) (Y n)] [∀ n, IsScalarTower S (A n) (Y n)]
    (f : ∀ n, X →ₗ[S] Y n) [∀ n, IsLocalizedModule n.asIdeal.primeCompl (f n)] :
    Module.length R X =
      ∑ n : MaximalSpectrum S, Module.length (A n) (Y n) * (n.asIdeal.inertiaDeg R : ℕ∞) := by sorry
