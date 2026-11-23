-- Prove2me | Theorems.Thm_GlobalTheory_localizationAtPrime_isDiscreteValuationRing_of_height_eq_one
-- name    : GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:27.720701+00:00
-- url     : https://prove2.me/theorems/91d038ce-a28b-4a8a-adfd-d07088a74422
-- title:
--   Global Theory: localization At Prime is Discrete Valuation Ring of height eq one
-- statement:
--   The Global Theory construction uses the localization At Prime is Discrete Valuation Ring of height eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationAtPrimeIsDiscreteValuationRingOfHeig.lean#L6-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/LocalizationAtPrimeIsDiscreteValuationRingOfHeig.lean#L6-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LocalizationAtPrimeIsDiscreteValuationRingOfHeig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.localizationAtPrime_isDiscreteValuationRing_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      (q : Ideal A) [q.IsPrime], q.height = 1 → IsDiscreteValuationRing (Localization.AtPrime q) := by sorry
