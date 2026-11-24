-- Prove2me | Theorems.Thm_GlobalTheory_exists_intCast_mem_of_isMaximal
-- name    : GlobalTheory.exists_intCast_mem_of_isMaximal
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:33:04.152812+00:00
-- url     : https://prove2.me/theorems/5b51cf81-5873-483e-8fed-04890628bb73
-- title:
--   Global Theory: exists int Cast mem of is Maximal
-- statement:
--   The Global Theory construction uses the exists int Cast mem of is Maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHorizontalPrimeLeOfIsMaximal.lean#L8-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsHorizontalPrimeLeOfIsMaximal.lean#L8-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHorizontalPrimeLeOfIsMaximal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_intCast_mem_of_isMaximal (R : Type*) [CommRing R] [Algebra.FiniteType ℤ R]
    (m : Ideal R) [m.IsMaximal] : ∃ p : ℤ, p ≠ 0 ∧ algebraMap ℤ R p ∈ m := by sorry
