-- Prove2me | Theorems.Thm_GlobalTheory_integralClosure_eq_iInf_discreteValuationSubring
-- name    : GlobalTheory.integralClosure_eq_iInf_discreteValuationSubring
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:56:21.663939+00:00
-- url     : https://prove2.me/theorems/07b1f362-2a19-42ce-abf8-5993326b9ba3
-- title:
--   Global Theory: integral Closure eq i Inf discrete Valuation Subring
-- statement:
--   The Global Theory construction uses the integral Closure eq i Inf discrete Valuation Subring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L411-L424
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L411-L424

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

theorem GlobalTheory.integralClosure_eq_iInf_discreteValuationSubring [Algebra.EssFiniteType R L] :
    (integralClosure R L).toSubring =
      ⨅ V : {V : ValuationSubring L // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring}, V.1.toSubring := by sorry
