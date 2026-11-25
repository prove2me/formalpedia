-- Prove2me | Theorems.Thm_GlobalTheory_exists_discreteValuationSubring_dominating_notMem
-- name    : GlobalTheory.exists_discreteValuationSubring_dominating_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:36:15.472805+00:00
-- url     : https://prove2.me/theorems/f880746b-486f-48fe-a809-3b140cf3fd2e
-- title:
--   Global Theory: exists discrete Valuation Subring dominating not Mem
-- statement:
--   The Global Theory construction uses the exists discrete Valuation Subring dominating not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L381-L409
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L381-L409

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
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
variable {R L : Type*} [CommRing R] [IsLocalRing R] [Field L]
variable [IsNoetherianRing R] [Algebra R L]

theorem GlobalTheory.exists_discreteValuationSubring_dominating_notMem [Algebra.EssFiniteType R L] {x : L}
    (hx : ¬ IsIntegral R x) :
    ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring ∧ x ∉ V := by sorry
