-- Prove2me | Theorems.Thm_GlobalTheory_range_algebraMap_eq_iInf_discreteValuationSubring
-- name    : GlobalTheory.range_algebraMap_eq_iInf_discreteValuationSubring
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:16:39.307174+00:00
-- url     : https://prove2.me/theorems/85513ff2-90d9-40a3-828e-f57d6a1826cb
-- title:
--   Global Theory: range algebra Map eq i Inf discrete Valuation Subring
-- statement:
--   The Global Theory construction uses the range algebra Map eq i Inf discrete Valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L577-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L577-L584

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
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem GlobalTheory.range_algebraMap_eq_iInf_discreteValuationSubring [IsIntegrallyClosed R] :
    (algebraMap R K).range =
      ⨅ V : {V : ValuationSubring K // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring}, V.1.toSubring := by sorry
