-- Prove2me | Theorems.Thm_GlobalTheory_length_restrictScalars_eq_finsum
-- name    : GlobalTheory.length_restrictScalars_eq_finsum
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:49:05.919363+00:00
-- url     : https://prove2.me/theorems/d04e6737-602b-4654-a688-9f8de1f56533
-- title:
--   Global Theory: length restrict Scalars eq finsum
-- statement:
--   The Global Theory construction uses the length restrict Scalars eq finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L186-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/LengthRestrictScalarsEqSumInertiaDegOfSubset.lean#L186-L194

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

theorem GlobalTheory.length_restrictScalars_eq_finsum {X : Type*} [AddCommGroup X] [Module S X]
    (h : IsFiniteLength S X) [Module R X] [IsScalarTower R S X] :
    Module.length R X = ∑ᶠ n : MaximalSpectrum S, Module.length (Localization.AtPrime n.asIdeal)
      (LocalizedModule n.asIdeal.primeCompl X) * Module.length R (S ⧸ n.asIdeal) := by sorry
