-- Prove2me | Theorems.Thm_GlobalTheory_discreteValuationRing_dominating_noetherian_local
-- name    : GlobalTheory.discreteValuationRing_dominating_noetherian_local
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:46:47.24686+00:00
-- url     : https://prove2.me/theorems/98330af7-7689-4f4f-8c30-f493e50df855
-- title:
--   Global Theory: discrete Valuation Ring dominating noetherian local
-- statement:
--   The Global Theory construction uses the discrete Valuation Ring dominating noetherian local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L704-L730
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L704-L730

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

theorem GlobalTheory.discreteValuationRing_dominating_noetherian_local (L : Type w) [Field L] [Algebra K L]
    [Algebra R L] [IsScalarTower R K L] [FiniteDimensional K L] :
    (¬ IsField R → ∃ V : ValuationSubring L, IsDiscreteValuationRing V ∧
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring) ∧
    (IsIntegrallyClosed R → (algebraMap R K).range =
      ⨅ V : {V : ValuationSubring K // IsDiscreteValuationRing V ∧
        LocalSubring.range (algebraMap R K) ≤ V.toLocalSubring}, V.1.toSubring) ∧
    ∀ (V : ValuationSubring L) [IsDiscreteValuationRing V],
      LocalSubring.range (algebraMap R L) ≤ V.toLocalSubring →
      IsDiscreteValuationRing (AdicCompletion (maximalIdeal V) V) ∧
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal V) V))
        (AdicCompletion (maximalIdeal V) V) ∧
      (∀ π : V, Irreducible π → Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π)) ∧
      ∃ h : ∀ r, algebraMap R L r ∈ V,
        Function.Injective ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp
          ((algebraMap R L).codRestrict V h)) ∧
        IsLocalHom ((algebraMap V (AdicCompletion (maximalIdeal V) V)).comp
          ((algebraMap R L).codRestrict V h)) := by sorry
