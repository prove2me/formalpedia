-- Prove2me | Theorems.Thm_GlobalTheory_unitMultiple_descends_of_height_eq_one
-- name    : GlobalTheory.unitMultiple_descends_of_height_eq_one
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:48.892962+00:00
-- url     : https://prove2.me/theorems/b09ee405-bbd5-46c1-bfcf-42199edfdcea
-- title:
--   Global Theory: unit Multiple descends of height eq one
-- statement:
--   The Global Theory construction uses the unit Multiple descends of height eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitOfDvrUnit.lean#L6-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsLocalUnitOfDvrUnit.lean#L6-L49

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalUnitOfDvrUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.unitMultiple_descends_of_height_eq_one :
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (𝔭 : PrimeSpectrum A),
    𝔭.asIdeal.height = 1 → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (iT : Localization.AtPrime 𝔭.asIdeal →+* V), Function.Injective iT → IsLocalHom iT →
    ∀ a b : A,
    (∃ w : Vˣ, iT (algebraMap A _ a) = iT (algebraMap A _ b) * w) →
    ∃ u : (Localization.AtPrime 𝔭.asIdeal)ˣ,
      (u : Localization.AtPrime 𝔭.asIdeal) * algebraMap A _ b = algebraMap A _ a := by sorry
